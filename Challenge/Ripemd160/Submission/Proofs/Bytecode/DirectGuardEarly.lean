import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 4887 is taken, the stub at pc 4952 drops the word and jumps to the appended
guard at pc 5028.  The eleven instructions are taken one at a time.
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 4952 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2966 (by rfl)
  have hblock : Decode.isValidJumpDest submissionBytecode 5028 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3009 (by rfl)
  rw [show sizeMatched input = stG input 4847 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 5028 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 2925 0 0)
    (blockOf _ (pcFactG input 2925 4847 [] (by norm_num) pc2819)
      (stepG_push0 input 4847 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 2926 .CALLDATALOAD)
    (blockOf _ (pcFactG input 2926 4848 [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 4848 ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 2927 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 2927 4849 [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 4849 (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := soundG (pushAt 2928 32 KnownInputData.fullWord)
    (blockOf _ (pcFactG input 2928 4850 [referenceWord input, referenceWord input]
        (by norm_num) pc2822)
      (stepG_push input 4850 32 KnownInputData.fullWord
        [referenceWord input, referenceWord input] (by simp) (by decide) (by decide)
        (by norm_num)))
  have step4 := soundG (opAt 2929 .XOR)
    (blockOf _ (pcFactG input 2929 4883
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 4883 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 2930 2 (UInt256.ofNat 4952))
    (blockOf _ (pcFactG input 2930 4884
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 4884 2 (UInt256.ofNat 4952)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 2931 .JUMPI)
    (blockOf _ (pcFactG input 2931 4887
        [UInt256.ofNat 4952,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 4887 4952
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 2966 .JUMPDEST)
    (blockOf _ (pcFactG input 2966 4952 [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 4952 [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 2967 .POP)
    (blockOf _ (pcFactG input 2967 4953 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 4953 (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 2968 2 (UInt256.ofNat 5028))
    (blockOf _ (pcFactG input 2968 4954 [] (by norm_num) pc2862)
      (stepG_push input 4954 2 (UInt256.ofNat 5028) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 2969 .JUMP)
    (blockOf _ (pcFactG input 2969 4957 [UInt256.ofNat 5028] (by norm_num) pc2863)
      (stepG_jump input 4957 5028 [] (by simp) (by norm_num) hblock))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
