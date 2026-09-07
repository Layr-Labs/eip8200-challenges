import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 5013 is taken, the stub at pc 5078 drops the word and falls through to the appended
guard at pc 5084. The repeated-word construction is lifted as one block;
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0x13d5 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3466 (by rfl)
  rw [show sizeMatched input = stG input 0x1386 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 0x13dc [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 3420 0 0)
    (blockOf _ (pcFactG input 3420 0x1386 [] (by norm_num) pc2819)
      (stepG_push0 input 0x1386 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 3421 .CALLDATALOAD)
    (blockOf _ (pcFactG input 3421 0x1387 [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 0x1387 ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 3422 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 3422 0x1388 [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 0x1388 (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := RepeatedByteWordSite.gasSteps_fullWord
    (initialState submissionBytecode input 0) [referenceWord input, referenceWord input]
    (by simp) rfl rfl rfl deployAddress_not_precompile
  have step4 := soundG (opAt 3429 .XOR)
    (blockOf _ (pcFactG input 3429 0x1391
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 0x1391 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 3430 2 (UInt256.ofNat 5078))
    (blockOf _ (pcFactG input 3430 0x1392
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 0x1392 2 (UInt256.ofNat 5078)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 3431 .JUMPI)
    (blockOf _ (pcFactG input 3431 0x1395
        [UInt256.ofNat 5078,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 0x1395 5078
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 3466 .JUMPDEST)
    (blockOf _ (pcFactG input 3466 0x13d5 [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 0x13d5 [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 3467 .POP)
    (blockOf _ (pcFactG input 3467 0x13d6 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 0x13d6 (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 3468 3 (UInt256.ofNat 5084))
    (blockOf _ (pcFactG input 3468 0x13d7 [] (by norm_num) pc2862)
      (stepG_push input 0x13d7 3 (UInt256.ofNat 5084) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 3469 .POP)
    (blockOf _ (pcFactG input 3469 0x13db [UInt256.ofNat 5084] (by norm_num) pc2863)
      (stepG_pop input 0x13db (UInt256.ofNat 5084) [] (by simp) (by norm_num)))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

#print axioms gasSteps_checkEarly

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
