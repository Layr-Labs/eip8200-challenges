import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 5142 is taken, the stub at pc 5204 drops the word and falls through to the appended
guard at pc 5210. The repeated-word construction is lifted as one block;
the remaining instructions are taken one at a time.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

private theorem refW_eq (input : ByteArray) :
    MachineState.readWord input ((⟨0⟩ : UInt256).toNat) = referenceWord input := rfl

def gasSteps_checkEarly (input : ByteArray)
    (href : referenceWord input ≠ KnownInputData.fullWord) :
    GasSteps (sizeMatched input) (PatternedScan.patternedEntry input) := by
  have hxor : UInt256.xor KnownInputData.fullWord (referenceWord input) ≠ 0 := by
    intro hz
    exact href ((KnownInputLogic.wordXor_eq_zero_iff
      KnownInputData.fullWord (referenceWord input)).1 hz).symm
  have htrue : UInt256.isTrue
      (UInt256.xor KnownInputData.fullWord (referenceWord input)) = true := by
    have h : UInt256.isTrue
        (UInt256.xor KnownInputData.fullWord (referenceWord input)) := by
      intro hnat
      apply hxor
      apply Challenge.EvmProof.Word.word_ext
      simpa using hnat
    simpa using h
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0x65 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 61 (by rfl)
  rw [show sizeMatched input = stG input 0x18 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 0x67 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 16 0 0)
    (blockOf _ (pcFactG input 16 0x18 [] (by norm_num) pc2819)
      (stepG_push0 input 0x18 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 17 .CALLDATALOAD)
    (blockOf _ (pcFactG input 17 0x19 [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 0x19 ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 18 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 18 0x1a [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 0x1a (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := RepeatedByteWordSite.gasSteps_fullWord
    (initialState submissionBytecode input 0) [referenceWord input, referenceWord input]
    (by simp) rfl rfl rfl deployAddress_not_precompile
  have step4 := soundG (opAt 25 .XOR)
    (blockOf _ (pcFactG input 25 0x23
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 0x23 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 26 1 (UInt256.ofNat 101))
    (blockOf _ (pcFactG input 26 0x24
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 0x24 1 (UInt256.ofNat 101)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 27 .JUMPI)
    (blockOf _ (pcFactG input 27 0x26
        [UInt256.ofNat 101,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 0x26 101
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 61 .JUMPDEST)
    (blockOf _ (pcFactG input 61 0x65 [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 0x65 [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 62 .POP)
    (blockOf _ (pcFactG input 62 0x66 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 0x66 (referenceWord input) [] (by simp) (by norm_num)))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans (step5.trans (step6.trans (step7.trans (step8))))))))

#print axioms gasSteps_checkEarly

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
