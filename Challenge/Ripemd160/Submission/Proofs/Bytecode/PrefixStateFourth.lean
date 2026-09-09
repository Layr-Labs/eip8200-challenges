import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateKernel

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

/-! A checked fourth-block extension of the promoted prefix ladder.
The first three blocks retain their existing mathematical certificates.
Words six and seven certify the fourth block for every remaining suffix. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateFourth

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PrefixStateModel

def nextState4 (s : State) (input : ByteArray) : State :=
  PrefixStateMemory.resultState4 (PrefixStateMemory.copied s) input

@[simp] theorem nextState4_executionEnv (s : State) (input : ByteArray) :
    (nextState4 s input).executionEnv = s.executionEnv := rfl
@[simp] theorem nextState4_halt (s : State) (input : ByteArray) :
    (nextState4 s input).halt = s.halt := rfl
@[simp] theorem nextState4_callStack (s : State) (input : ByteArray) :
    (nextState4 s input).callStack = s.callStack := rfl

theorem nextState4_word_above (s : State) (input : ByteArray) (address : Nat)
    (ha : 0x2e0 ≤ address) :
    StackRunBridge.wordAt (nextState4 s input) address = StackRunBridge.wordAt s address :=
  (PrefixStateMemory.resultState4_word_above _ _ _ (by omega)).trans
    (PrefixStateMemory.copied_word_above _ _ (by omega))

theorem quadruple_blockCount (input : ByteArray) (hq : quadruple input = true) :
    4 ≤ DriverTrace.blockCount input := by
  have h := (quadruple_iff input).1 hq
  have hsize := PrefixStateData.size_ge_256_of_words input h.2.2.2.2
  unfold DriverTrace.blockCount Padding.paddedLength
  omega

theorem hashAfter_four (input : ByteArray)
    (h : Matched input ∧ Matched2 input ∧ Matched3 input ∧ Matched4 input) :
    CompressionSeamBridge.hashAfter input 4 = PatternedDigest.H4 := by
  have e4 : CompressionSeamBridge.hashAfter input 4 =
      Crypto.Ripemd160.compressBlock (CompressionSeamBridge.hashAfter input 3)
        (Padding.paddedMessage input) (3 * 64) := StackRunBridge.hashAfter_succ input 3
  rw [e4, PrefixStateKernel.hashAfter_three input ⟨h.1, h.2.1, h.2.2.1⟩]
  exact PrefixStateData.h_fourthBlock input h.2.2.2.1 h.2.2.2.2

theorem nextState4_hash (s : State) (input : ByteArray) (hq : quadruple input = true) :
    StackRunBridge.hashAt32 (nextState4 s input) =
      StackRunBridge.embedHashArray (CompressionSeamBridge.hashAfter input 4) := by
  have h := (quadruple_iff input).1 hq
  change StackMemory.hashAt (PrefixStateMemory.resultState4 (PrefixStateMemory.copied s) input).memory = _
  rw [PrefixStateMemory.resultState4_hash, hashAfter_four input h]
  rfl

#print axioms nextState4_hash
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateFourth
