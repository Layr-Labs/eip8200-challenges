import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 5307 is taken, the stub at pc 5372 drops the word and jumps to the appended
guard at pc 5448.  The eleven instructions are taken one at a time.
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 5372 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2827 (by rfl)
  have hblock : Decode.isValidJumpDest submissionBytecode 5448 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2870 (by rfl)
  rw [show sizeMatched input = stG input 5267 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 5448 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 2786 0 0)
    (blockOf _ (pcFactG input 2786 5267 [] (by norm_num) pc2819)
      (stepG_push0 input 5267 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 2787 .CALLDATALOAD)
    (blockOf _ (pcFactG input 2787 5268 [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 5268 ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 2788 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 2788 5269 [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 5269 (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := soundG (pushAt 2789 32 KnownInputData.fullWord)
    (blockOf _ (pcFactG input 2789 5270 [referenceWord input, referenceWord input]
        (by norm_num) pc2822)
      (stepG_push input 5270 32 KnownInputData.fullWord
        [referenceWord input, referenceWord input] (by simp) (by decide) (by decide)
        (by norm_num)))
  have step4 := soundG (opAt 2790 .XOR)
    (blockOf _ (pcFactG input 2790 5303
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 5303 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 2791 2 (UInt256.ofNat 5372))
    (blockOf _ (pcFactG input 2791 5304
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 5304 2 (UInt256.ofNat 5372)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 2792 .JUMPI)
    (blockOf _ (pcFactG input 2792 5307
        [UInt256.ofNat 5372,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 5307 5372
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 2827 .JUMPDEST)
    (blockOf _ (pcFactG input 2827 5372 [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 5372 [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 2828 .POP)
    (blockOf _ (pcFactG input 2828 5373 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 5373 (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 2829 2 (UInt256.ofNat 5448))
    (blockOf _ (pcFactG input 2829 5374 [] (by norm_num) pc2862)
      (stepG_push input 5374 2 (UInt256.ofNat 5448) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 2830 .JUMP)
    (blockOf _ (pcFactG input 2830 5377 [UInt256.ofNat 5448] (by norm_num) pc2863)
      (stepG_jump input 5377 5448 [] (by simp) (by norm_num) hblock))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
