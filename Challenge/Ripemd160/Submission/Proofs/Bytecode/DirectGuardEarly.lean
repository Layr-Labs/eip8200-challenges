import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 4873 is taken, the stub at pc 4938 drops the word and jumps to the appended
guard at pc 5014.  The eleven instructions are taken one at a time.
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 4938 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2952 (by rfl)
  have hblock : Decode.isValidJumpDest submissionBytecode 5014 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2995 (by rfl)
  rw [show sizeMatched input = stG input 4833 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 5014 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 2911 0 0)
    (blockOf _ (pcFactG input 2911 4833 [] (by norm_num) pc2819)
      (stepG_push0 input 4833 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 2912 .CALLDATALOAD)
    (blockOf _ (pcFactG input 2912 4834 [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 4834 ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 2913 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 2913 4835 [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 4835 (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := soundG (pushAt 2914 32 KnownInputData.fullWord)
    (blockOf _ (pcFactG input 2914 4836 [referenceWord input, referenceWord input]
        (by norm_num) pc2822)
      (stepG_push input 4836 32 KnownInputData.fullWord
        [referenceWord input, referenceWord input] (by simp) (by decide) (by decide)
        (by norm_num)))
  have step4 := soundG (opAt 2915 .XOR)
    (blockOf _ (pcFactG input 2915 4869
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 4869 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 2916 2 (UInt256.ofNat 4938))
    (blockOf _ (pcFactG input 2916 4870
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 4870 2 (UInt256.ofNat 4938)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 2917 .JUMPI)
    (blockOf _ (pcFactG input 2917 4873
        [UInt256.ofNat 4938,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 4873 4938
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 2952 .JUMPDEST)
    (blockOf _ (pcFactG input 2952 4938 [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 4938 [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 2953 .POP)
    (blockOf _ (pcFactG input 2953 4939 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 4939 (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 2954 2 (UInt256.ofNat 5014))
    (blockOf _ (pcFactG input 2954 4940 [] (by norm_num) pc2862)
      (stepG_push input 4940 2 (UInt256.ofNat 5014) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 2955 .JUMP)
    (blockOf _ (pcFactG input 2955 4943 [UInt256.ofNat 5014] (by norm_num) pc2863)
      (stepG_jump input 4943 5014 [] (by simp) (by norm_num) hblock))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
