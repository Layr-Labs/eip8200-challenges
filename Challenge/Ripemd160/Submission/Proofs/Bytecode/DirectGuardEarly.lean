import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 4885 is taken, the stub at pc 4950 drops the word and jumps to the appended
guard at pc 4956.  The eleven instructions are taken one at a time.
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 4950 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3032 (by rfl)
  have hblock : Decode.isValidJumpDest submissionBytecode 4956 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3036 (by rfl)
  rw [show sizeMatched input = stG input 4845 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 4956 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 2991 0 0)
    (blockOf _ (pcFactG input 2991 4845 [] (by norm_num) pc2819)
      (stepG_push0 input 4845 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 2992 .CALLDATALOAD)
    (blockOf _ (pcFactG input 2992 4846 [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 4846 ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 2993 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 2993 4847 [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 4847 (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := soundG (pushAt 2994 32 KnownInputData.fullWord)
    (blockOf _ (pcFactG input 2994 4848 [referenceWord input, referenceWord input]
        (by norm_num) pc2822)
      (stepG_push input 4848 32 KnownInputData.fullWord
        [referenceWord input, referenceWord input] (by simp) (by decide) (by decide)
        (by norm_num)))
  have step4 := soundG (opAt 2995 .XOR)
    (blockOf _ (pcFactG input 2995 4881
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 4881 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 2996 2 (UInt256.ofNat 4950))
    (blockOf _ (pcFactG input 2996 4882
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 4882 2 (UInt256.ofNat 4950)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 2997 .JUMPI)
    (blockOf _ (pcFactG input 2997 4885
        [UInt256.ofNat 4950,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 4885 4950
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 3032 .JUMPDEST)
    (blockOf _ (pcFactG input 3032 4950 [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 4950 [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 3033 .POP)
    (blockOf _ (pcFactG input 3033 4951 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 4951 (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 3034 2 (UInt256.ofNat 4956))
    (blockOf _ (pcFactG input 3034 4952 [] (by norm_num) pc2862)
      (stepG_push input 4952 2 (UInt256.ofNat 4956) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 3035 .JUMP)
    (blockOf _ (pcFactG input 3035 4955 [UInt256.ofNat 4956] (by norm_num) pc2863)
      (stepG_jump input 4955 4956 [] (by simp) (by norm_num) hblock))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
