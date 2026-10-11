import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTable
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerFunctional
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadSkipEntry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerIteration
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable

def states (input : ByteArray) : Nat → State
  | 0 => PadSkipEntry.entryState input
  | n + 1 => scheduledState (states input n) n

def hashes (input : ByteArray) : Nat → Compression.HashState
  | 0 => StackRunBridge.initialHashState
  | n + 1 => PersistentStaggerFunctional.result (states input (n + 1)).memory (hashes input n)

@[simp] theorem states_zero (input : ByteArray) : states input 0 = PadSkipEntry.entryState input := rfl
@[simp] theorem states_succ (input : ByteArray) (n : Nat) :
    states input (n + 1) = scheduledState (states input n) n := rfl
@[simp] theorem hashes_zero (input : ByteArray) : hashes input 0 = StackRunBridge.initialHashState := rfl
@[simp] theorem hashes_succ (input : ByteArray) (n : Nat) :
    hashes input (n + 1) =
      PersistentStaggerFunctional.result (scheduledState (states input n) n).memory (hashes input n) := rfl

theorem states_executionEnv (input : ByteArray) (n : Nat) :
    (states input n).executionEnv = (PadSkipEntry.entryState input).executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => exact (scheduled_env _ n).trans ih

theorem states_halt (input : ByteArray) (n : Nat) : (states input n).halt = .Running := by
  induction n with
  | zero => exact PadSkipEntry.entryState_halt input
  | succ n ih => exact (scheduled_halt _ n).trans ih

theorem states_callStack (input : ByteArray) (n : Nat) : (states input n).callStack = [] := by
  induction n with
  | zero => exact PadSkipEntry.entryState_callStack input
  | succ n ih => exact (scheduled_callStack _ n).trans ih

theorem states_calldata (input : ByteArray) (n : Nat) :
    (states input n).executionEnv.calldata = input := by
  rw [states_executionEnv]
  exact PadSkipEntry.entryState_calldata input

theorem states_code (input : ByteArray) (n : Nat) :
    (states input n).executionEnv.code = submissionBytecode := by
  rw [states_executionEnv]
  exact PadSkipEntry.entryState_code input

theorem states_fork (input : ByteArray) (n : Nat) : (states input n).fork = .Osaka := by
  change (states input n).executionEnv.fork = .Osaka
  rw [states_executionEnv]
  exact PadSkipEntry.entryState_fork input

theorem states_noPrecompile (input : ByteArray) (n : Nat) :
    Precompile.isPrecompileWithConfig (states input n).executionEnv.precompileConfig
      (states input n).executionEnv.fork (states input n).executionEnv.codeAddr = false := by
  rw [states_executionEnv]
  exact PadSkipEntry.entryState_noPrecompile input

theorem initial_context (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size) :
    Context (PadSkipEntry.entryState input) input 0 :=
  ⟨PadSkipEntry.entryState_calldata input, PadSkipEntry.entryState_active input hfit hpos,
    PadSkipEntry.entryState_allocated input hfit, (fun i _ hi hn => PadSkipEntry.entryState_blockAt input hfit i hi hn),
    fun i hi => PaddedBlockBridge.padReturned_blockIndexSeparated input hfit i hi,
    fun a ha => PadSkipEntry.entryState_zero_below input hfit a
      (by have := (PoolShapeV2.zeroAddressesV2_band a ha).2.1
          change a < 1056
          omega)⟩

theorem states_context (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size)
    (n : Nat) (hn : n ≤ DriverTrace.blockCount input) : Context (states input n) input n := by
  induction n with
  | zero => exact initial_context input hfit hpos
  | succ n ih =>
    exact Context.scheduled (states input n) input n hfit (by omega) (ih (by omega))

theorem states_activeWords (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size)
    (n : Nat) (hn : n ≤ DriverTrace.blockCount input) :
    (states input n).activeWords = (PadSkipEntry.entryState input).activeWords := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (scheduled_active_eq (states input n) input n hfit (by omega)
      (states_context input hfit hpos n (by omega))).trans (ih (by omega))

theorem states_word_above (input : ByteArray) (n address : Nat) (ha : 1120 ≤ address) :
    MachineState.readWord (states input n).memory address =
      MachineState.readWord (PadSkipEntry.entryState input).memory address := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (scheduled_word_above (states input n) n address ha).trans ih

theorem states_ready (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size)
    (n : Nat) (hn : n < DriverTrace.blockCount input) :
    StaggerMessage.Ready (states input (n + 1)).memory (blockWords input n) :=
  ready (states input n) input n hfit hn (states_context input hfit hpos n (by omega))

theorem hashArray_hashes (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size)
    (n : Nat) (hn : n ≤ DriverTrace.blockCount input) :
    CompressionCorrect.hashArray (hashes input n) = CompressionSeamBridge.hashAfter input n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hashes]
    rw [PersistentStaggerFunctional.result_compressBlock
      (states input (n + 1)).memory (Padding.paddedMessage input)
      (DriverTrace.blockOffset n) (hashes input n) (states_ready input hfit hpos n (by omega))]
    rw [ih (by omega), StackRunBridge.hashAfter_succ]
    rfl

/-- What the block-exit `MSIZE` reads after block `i`: exactly the end of the copied input on
the fast entry when the pad-only block is next, and above the next block pointer otherwise. -/
theorem states_msize (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size)
    (i : Nat) (hi : i + 1 < DriverTrace.blockCount input) :
    ((input.size = (i + 1) * 64 ∧ input.size < 256) →
        UInt256.ofNat (32 * (states input (i + 1)).activeWords.toNat) =
          DriverTrace.messageOffsetWord (i + 1)) ∧
      (¬ (input.size = (i + 1) * 64 ∧ input.size < 256) →
        UInt256.ofNat (32 * (states input (i + 1)).activeWords.toNat) ≠
          DriverTrace.messageOffsetWord (i + 1)) := by
  have hsize : input.size < 2 ^ 64 := hfit
  have hctx := states_context input hfit hpos (i + 1) (by omega)
  have hact := states_activeWords input hfit hpos (i + 1) (by omega)
  have hle := PaddingTrace.entryState_active_le input hfit
  have hcount : DriverTrace.blockCount input * 64 < input.size + 73 := by
    rw [← DriverTrace.paddedLength_eq_blockCount]
    exact Padding.paddedLength_lt input.size
  constructor
  · intro hh
    rw [hact]
    change UInt256.ofNat (32 * (PaddingTrace.entryState input).activeWords.toNat) = _
    rw [PaddingTrace.entryState_msize_aligned input hfit (by omega) hpos]
    unfold DriverTrace.messageOffsetWord DriverTrace.blockOffset Padding.messageOffset
    congr 1
    omega
  · intro hh heq
    have hal := hctx.allocated (i + 1) hi (by unfold DriverTrace.blockOffset; exact hh)
    have hA : (states input (i + 1)).activeWords.toNat ≤ 2 ^ 70 := by
      rw [hact]; exact hle
    have ht := congrArg UInt256.toNat heq
    unfold DriverTrace.messageOffsetWord DriverTrace.blockOffset Padding.messageOffset at ht
    rw [Word.word_toNat_ofNat, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
    unfold messagePointer Padding.messageOffset DriverTrace.blockOffset at hal
    omega

#print axioms initial_context
#print axioms states_context
#print axioms states_activeWords
#print axioms states_ready
#print axioms hashArray_hashes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerIteration
