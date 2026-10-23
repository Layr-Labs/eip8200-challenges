import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PersistentStaggerTable
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerFunctional
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PaddedBlockBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PadSkipEntry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ColdOrdinaryBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerPersistentLoopInduction
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PersistentStaggerIteration
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open HoistedInherited.PersistentStaggerTable

def states (input : ByteArray) : Nat → State
  | 0 => HoistedInherited.PadSkipEntry.entryState input
  | n + 1 => scheduledState (states input n) n

def hashes (input : ByteArray) : Nat → Compression.HashState
  | 0 => StackRunBridge.initialHashState
  | n + 1 => PersistentStaggerFunctional.result (states input (n + 1)).memory (hashes input n)

@[simp] theorem states_zero (input : ByteArray) : states input 0 = HoistedInherited.PadSkipEntry.entryState input := rfl
@[simp] theorem states_succ (input : ByteArray) (n : Nat) :
    states input (n + 1) = scheduledState (states input n) n := rfl
@[simp] theorem hashes_zero (input : ByteArray) : hashes input 0 = StackRunBridge.initialHashState := rfl
@[simp] theorem hashes_succ (input : ByteArray) (n : Nat) :
    hashes input (n + 1) =
      PersistentStaggerFunctional.result (scheduledState (states input n) n).memory (hashes input n) := rfl

theorem states_executionEnv (input : ByteArray) (n : Nat) :
    (states input n).executionEnv = (HoistedInherited.PadSkipEntry.entryState input).executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => exact (scheduled_env _ n).trans ih

theorem states_halt (input : ByteArray) (n : Nat) : (states input n).halt = .Running := by
  induction n with
  | zero => exact HoistedInherited.PadSkipEntry.entryState_halt input
  | succ n ih => exact (scheduled_halt _ n).trans ih

theorem states_callStack (input : ByteArray) (n : Nat) : (states input n).callStack = [] := by
  induction n with
  | zero => exact HoistedInherited.PadSkipEntry.entryState_callStack input
  | succ n ih => exact (scheduled_callStack _ n).trans ih

theorem states_calldata (input : ByteArray) (n : Nat) :
    (states input n).executionEnv.calldata = input := by
  rw [states_executionEnv]
  exact HoistedInherited.PadSkipEntry.entryState_calldata input

theorem states_code (input : ByteArray) (n : Nat) :
    (states input n).executionEnv.code = submissionBytecode := by
  rw [states_executionEnv]
  exact HoistedInherited.PadSkipEntry.entryState_code input

theorem states_fork (input : ByteArray) (n : Nat) : (states input n).fork = .Osaka := by
  change (states input n).executionEnv.fork = .Osaka
  rw [states_executionEnv]
  exact HoistedInherited.PadSkipEntry.entryState_fork input

theorem states_noPrecompile (input : ByteArray) (n : Nat) :
    Precompile.isPrecompileWithConfig (states input n).executionEnv.precompileConfig
      (states input n).executionEnv.fork (states input n).executionEnv.codeAddr = false := by
  rw [states_executionEnv]
  exact HoistedInherited.PadSkipEntry.entryState_noPrecompile input

theorem initial_context (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size) :
    Context (HoistedInherited.PadSkipEntry.entryState input) input 0 :=
  ⟨HoistedInherited.PadSkipEntry.entryState_calldata input, HoistedInherited.PadSkipEntry.entryState_active input hfit hpos,
    HoistedInherited.PadSkipEntry.entryState_allocated input hfit, (fun i _ hi hn => HoistedInherited.PadSkipEntry.entryState_blockAt input hfit i hi hn),
    fun i hi => HoistedInherited.PaddedBlockBridge.padReturned_blockIndexSeparated input hfit i hi,
    fun a ha => HoistedInherited.PadSkipEntry.entryState_zero_below input hfit a
      (by have := (HoistedInherited.PoolShapeV2.zeroAddressesV2_band a ha).2.1
          change a < 1056
          omega)
      (by have := (HoistedInherited.PoolShapeV2.zeroAddressesV2_band a ha).2.2
          exact ⟨by omega, by omega⟩)⟩

theorem states_context (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size)
    (n : Nat) (hn : n ≤ DriverTrace.blockCount input) : Context (states input n) input n := by
  induction n with
  | zero => exact initial_context input hfit hpos
  | succ n ih =>
    exact Context.scheduled (states input n) input n hfit (by omega) (ih (by omega))

theorem states_activeWords (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size)
    (n : Nat) (hn : n ≤ DriverTrace.blockCount input) :
    (states input n).activeWords = (HoistedInherited.PadSkipEntry.entryState input).activeWords := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (scheduled_active_eq (states input n) input n hfit (by omega)
      (states_context input hfit hpos n (by omega))).trans (ih (by omega))

theorem states_word_above (input : ByteArray) (n address : Nat) (ha : 1120 ≤ address) :
    MachineState.readWord (states input n).memory address =
      MachineState.readWord (HoistedInherited.PadSkipEntry.entryState input).memory address := by
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

/-- A block consumes its selected continuation and exposes its old `h2` word.
The pad-only entry accepts the garbage left by the preceding dispatch. -/
def gasSteps_block (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size)
    (i : Nat) (hi : i < DriverTrace.blockCount input)
    (rho : List UInt256) (hs : rho.length ≤ 880)
    (tail : List UInt256)
    (hrho : rho = DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: tail) :
    GasSteps
      (HoistedInherited.StaggerPersistentLoopInduction.loopState input (states input i)
        (hashes input (i - 1)) (hashes input i) i (DriverTrace.blockCount input) rho)
      (HoistedInherited.StaggerPersistentLoopInduction.postState input (states input (i + 1))
        (hashes input i) (hashes input (i + 1)) i (DriverTrace.blockCount input) rho) := by
  have gb := HoistedInherited.ColdOrdinaryBlock.gasSteps (states input i) input i (hashes input i)
    (HoistedInherited.StaggerPersistentLoopInduction.loopCont input (hashes input (i - 1)) i)
    rho hs tail hrho hfit hi (states_context input hfit hpos i (Nat.le_of_lt hi))
    (states_code input i) (states_fork input i) (states_halt input i)
    (states_noPrecompile input i)
  simpa only [HoistedInherited.StaggerPersistentLoopInduction.loopState,
    HoistedInherited.StaggerPersistentLoopInduction.postState, HoistedInherited.StaggerPersistentLoopInduction.blockOff,
    HoistedInherited.StaggerPersistentLoopInduction.offsetWord, states_succ, hashes_succ,
    HoistedInherited.StaggerPersistentLoopInduction.blockCont_loopCont] using gb

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
  have hle := HoistedInherited.PaddingTrace.entryState_active_le input hfit
  have hcount : DriverTrace.blockCount input * 64 < input.size + 73 := by
    rw [← DriverTrace.paddedLength_eq_blockCount]
    exact Padding.paddedLength_lt input.size
  constructor
  · intro hh
    rw [hact]
    change UInt256.ofNat (32 * (HoistedInherited.PaddingTrace.entryState input).activeWords.toNat) = _
    rw [HoistedInherited.PaddingTrace.entryState_msize_aligned input hfit (by omega) hpos]
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

/-- What the generic last-block test reads after block `i` of a cold input: the active size is
below `off + 128` exactly after the last block.  The active size covers the padded message and
ends at most one word past it (the ninth footer byte of a 2^64-bit length). -/
theorem states_last (input : ByteArray) (hfit : CalldataFits input) (hpos : 0 < input.size)
    (hcold : ¬ (input.size % 64 = 0 ∧ input.size < 256))
    (i : Nat) (hi : i < DriverTrace.blockCount input) :
    ((UInt256.ofNat (32 * (states input (i + 1)).activeWords.toNat)).toNat <
        (DriverTrace.messageOffsetWord i + UInt256.ofNat 128).toNat ↔
      i + 1 = DriverTrace.blockCount input) := by
  have hsize : input.size < 2 ^ 64 := hfit
  have hact := states_activeWords input hfit hpos (i + 1) (by omega)
  have hentry : HoistedInherited.PadSkipEntry.entryState input = HoistedInherited.PaddingTrace.padReturned input :=
    HoistedInherited.PaddingTrace.entryState_miss input hcold
  have hlo := HoistedInherited.PaddingTrace.padReturned_allocated input hfit
  have hup := HoistedInherited.PaddingTrace.padReturned_active_upper input hfit
  have hP := DriverTrace.paddedLength_eq_blockCount input
  have hPlt := Padding.paddedLength_lt input.size
  have hPmod : Padding.paddedLength input.size % 64 = 0 := by unfold Padding.paddedLength; omega
  rw [hact, hentry]
  set aw := (HoistedInherited.PaddingTrace.padReturned input).activeWords.toNat with haw
  unfold Padding.messageOffset at hlo hup
  have hm : (UInt256.ofNat (32 * aw)).toNat = 32 * aw := by
    rw [Word.word_toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ho : (DriverTrace.messageOffsetWord i + UInt256.ofNat 128).toNat = 1056 + i * 64 + 128 := by
    unfold DriverTrace.messageOffsetWord DriverTrace.blockOffset Padding.messageOffset
    rw [Word.ofNat_add_ofNat (by omega), Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hm, ho]
  constructor
  · intro h
    by_contra hne
    omega
  · intro h
    omega

#print axioms initial_context
#print axioms states_context
#print axioms states_activeWords
#print axioms states_ready
#print axioms hashArray_hashes
#print axioms gasSteps_block
#print axioms states_last
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PersistentStaggerIteration
