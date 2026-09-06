import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 4931 is taken, the stub at pc 4996 drops the word and jumps to the appended
guard at pc 5072.  The eleven instructions are taken one at a time.
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 4996 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2847 (by rfl)
  have hblock : Decode.isValidJumpDest submissionBytecode 5072 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2890 (by rfl)
  rw [show sizeMatched input = stG input 4891 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 5072 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 2806 0 0)
    (blockOf _ (pcFactG input 2806 4891 [] (by norm_num) pc2819)
      (stepG_push0 input 4891 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 2807 .CALLDATALOAD)
    (blockOf _ (pcFactG input 2807 4892 [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 4892 ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 2808 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 2808 4893 [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 4893 (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := soundG (pushAt 2809 32 KnownInputData.fullWord)
    (blockOf _ (pcFactG input 2809 4894 [referenceWord input, referenceWord input]
        (by norm_num) pc2822)
      (stepG_push input 4894 32 KnownInputData.fullWord
        [referenceWord input, referenceWord input] (by simp) (by decide) (by decide)
        (by norm_num)))
  have step4 := soundG (opAt 2810 .XOR)
    (blockOf _ (pcFactG input 2810 4927
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 4927 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 2811 2 (UInt256.ofNat 4996))
    (blockOf _ (pcFactG input 2811 4928
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 4928 2 (UInt256.ofNat 4996)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 2812 .JUMPI)
    (blockOf _ (pcFactG input 2812 4931
        [UInt256.ofNat 4996,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 4931 4996
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 2847 .JUMPDEST)
    (blockOf _ (pcFactG input 2847 4996 [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 4996 [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 2848 .POP)
    (blockOf _ (pcFactG input 2848 4997 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 4997 (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 2849 2 (UInt256.ofNat 5072))
    (blockOf _ (pcFactG input 2849 4998 [] (by norm_num) pc2862)
      (stepG_push input 4998 2 (UInt256.ofNat 5072) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 2850 .JUMP)
    (blockOf _ (pcFactG input 2850 5001 [UInt256.ofNat 5072] (by norm_num) pc2863)
      (stepG_jump input 5001 5072 [] (by simp) (by norm_num) hblock))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
