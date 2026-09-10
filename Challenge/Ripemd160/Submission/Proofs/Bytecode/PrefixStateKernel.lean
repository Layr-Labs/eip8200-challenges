import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateData

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateKernel
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PrefixStateModel

def nextState (s : State) (input : ByteArray) (i : Nat) : State :=
  if input.size = 0 then FastEmptyBlock.resultState s input i
  else if i = 0 ∧ Matched input then PrefixStateMemory.resultState (PrefixStateMemory.copied s) input i
  else PairedBlockModel.resultState (prepared s i) input i

@[simp] theorem nextState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).executionEnv = s.executionEnv := by
  unfold nextState
  split
  · simp
  · split <;> simp
@[simp] theorem nextState_halt (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).halt = s.halt := by
  unfold nextState
  split
  · simp
  · split <;> simp
@[simp] theorem nextState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).callStack = s.callStack := by
  unfold nextState
  split
  · simp
  · split <;> simp

theorem nextState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (ha : 0x2e0 ≤ address) :
    StackRunBridge.wordAt (nextState s input i) address = StackRunBridge.wordAt s address := by
  unfold nextState
  split
  · exact FastEmptyBlock.resultState_word_above _ _ _ _ (by omega)
  · split
    · exact (PrefixStateMemory.resultState_word_above _ _ _ _ (by omega)).trans
        (PrefixStateMemory.copied_word_above _ _ (by omega))
    · exact (PairedBlockModel.resultState_word_above _ _ _ _ ha).trans
        (prepared_word_above _ _ _ (by omega))

def preparedContext (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    StackRunBridge.BlockContext (prepared s i) input i h where
  calldata := by simpa using ctx.calldata
  separated := ctx.separated
  messageBlock := by
    intro k hk
    unfold ScheduleCorrect.expectedWord Schedule.readLEWord
    rw [prepared_word_above _ _ _ (by have hh := ctx.separated k hk; omega)]
    exact ctx.messageBlock k hk
  hash := by
    unfold StackRunBridge.hashAt32 StackRunBridge.wordAt
    rw [prepared_word_above _ _ 32 (by omega), prepared_word_above _ _ 64 (by omega),
      prepared_word_above _ _ 96 (by omega), prepared_word_above _ _ 128 (by omega),
      prepared_word_above _ _ 160 (by omega)]
    exact ctx.hash

private theorem input_eq_empty (input : ByteArray) (hempty : input.size = 0) :
    input = ByteArray.empty := by
  apply ByteArray.ext
  apply Array.ext
  · simpa using hempty
  · intro i hi
    simp [hempty] at hi

theorem nextState_hash (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (hmodel : CompressionCorrect.hashArray h = CompressionSeamBridge.hashAfter input i) :
    StackRunBridge.hashAt32 (nextState s input i) =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
  unfold nextState
  by_cases hempty : input.size = 0
  · rw [if_pos hempty]
    have hinput := input_eq_empty input hempty
    subst input
    have hi0 : i = 0 := by
      simp [DriverTrace.blockCount, Padding.paddedLength] at hi
      omega
    subst i
    change StackMemory.hashAt (FastEmptyBlock.resultState s ByteArray.empty 0).memory = _
    rw [FastEmptyBlock.resultState_hashAt, hmodel]
    change FastEmptyBlock.emptyHash = StackRunBridge.embedHashArray
      (Crypto.Ripemd160.compressBlock Crypto.Ripemd160.H0 (Padding.paddedMessage ByteArray.empty) 0)
    rw [FastEmptyBlock.compress_empty]
    rfl
  · rw [if_neg hempty]
    by_cases hhit : i = 0 ∧ Matched input
    · rw [if_pos hhit]
      rcases hhit with ⟨rfl,hmatch⟩
      change StackMemory.hashAt (PrefixStateMemory.resultState (PrefixStateMemory.copied s) input 0).memory = _
      rw [PrefixStateMemory.resultState_hash, hmodel]
      change PrefixStateMemory.hash = StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock PatternedDigest.H0 (Padding.paddedMessage input) 0)
      rw [PrefixStateData.h8_firstBlock input hmatch.1 hmatch.2]
      rfl
    · rw [if_neg hhit]
      exact PairedBlockModel.resultState_hash _ _ _ _ (preparedContext s input i h ctx)

#print axioms nextState_hash

/-! ## The depth-2 rung as a two-block kernel step -/

/-- Two blocks consumed by the dispatcher: `H2` installed over the copied scratch state. -/
def nextState2 (s : State) (input : ByteArray) : State :=
  PrefixStateMemory.resultState2 (PrefixStateMemory.copied s) input

@[simp] theorem nextState2_executionEnv (s : State) (input : ByteArray) :
    (nextState2 s input).executionEnv = s.executionEnv := rfl
@[simp] theorem nextState2_halt (s : State) (input : ByteArray) :
    (nextState2 s input).halt = s.halt := rfl
@[simp] theorem nextState2_callStack (s : State) (input : ByteArray) :
    (nextState2 s input).callStack = s.callStack := rfl

theorem nextState2_word_above (s : State) (input : ByteArray) (address : Nat)
    (ha : 0x2e0 ≤ address) :
    StackRunBridge.wordAt (nextState2 s input) address = StackRunBridge.wordAt s address :=
  (PrefixStateMemory.resultState2_word_above _ _ _ (by omega)).trans
    (PrefixStateMemory.copied_word_above _ _ (by omega))

/-- The retained two-block interface is disabled by the compact dispatcher. -/
theorem double_blockCount (input : ByteArray) (hd : double input = true) :
    2 ≤ DriverTrace.blockCount input := by
  simp [double] at hd

/-- The chaining state after two blocks of a four-word match is `H2`. -/
theorem hashAfter_two (input : ByteArray) (h : Matched input ∧ Matched2 input) :
    CompressionSeamBridge.hashAfter input 2 = PatternedDigest.H2 := by
  have e2 : CompressionSeamBridge.hashAfter input 2 =
      Crypto.Ripemd160.compressBlock (CompressionSeamBridge.hashAfter input 1)
        (Padding.paddedMessage input) (1 * 64) := StackRunBridge.hashAfter_succ input 1
  have e1 : CompressionSeamBridge.hashAfter input 1 =
      Crypto.Ripemd160.compressBlock (CompressionSeamBridge.hashAfter input 0)
        (Padding.paddedMessage input) (0 * 64) := StackRunBridge.hashAfter_succ input 0
  have e0 : CompressionSeamBridge.hashAfter input 0 = PatternedDigest.H0 := rfl
  rw [e2, e1, e0, show 0 * 64 = 0 from rfl, show 1 * 64 = 64 from rfl,
    PrefixStateData.h8_firstBlock input h.1.1 h.1.2]
  exact PrefixStateData.h_secondBlock input h.2.1 h.2.2

theorem nextState2_hash (s : State) (input : ByteArray) (hd : double input = true) :
    StackRunBridge.hashAt32 (nextState2 s input) =
      StackRunBridge.embedHashArray (CompressionSeamBridge.hashAfter input 2) := by
  simp [double] at hd

#print axioms nextState2_hash
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateKernel
