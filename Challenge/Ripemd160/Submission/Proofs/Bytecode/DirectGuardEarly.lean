import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 4972 is taken, the stub at pc 5037 drops the word and falls through to the appended
guard at pc 5043. The repeated-word construction is lifted as one block;
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0x13ad = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3455 (by rfl)
  rw [show sizeMatched input = stG input 0x135d [] from rfl,
    show PatternedScan.patternedEntry input = stG input 0x13b3 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 3409 0 0)
    (blockOf _ (pcFactG input 3409 0x135d [] (by norm_num) pc2819)
      (stepG_push0 input 0x135d [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 3410 .CALLDATALOAD)
    (blockOf _ (pcFactG input 3410 0x135e [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 0x135e ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 3411 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 3411 0x135f [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 0x135f (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := RepeatedByteWordSite.gasSteps_fullWord
    (initialState submissionBytecode input 0) [referenceWord input, referenceWord input]
    (by simp) rfl rfl rfl deployAddress_not_precompile
  have step4 := soundG (opAt 3418 .XOR)
    (blockOf _ (pcFactG input 3418 0x1368
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 0x1368 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 3419 2 (UInt256.ofNat 5037))
    (blockOf _ (pcFactG input 3419 0x1369
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 0x1369 2 (UInt256.ofNat 5037)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 3420 .JUMPI)
    (blockOf _ (pcFactG input 3420 0x136c
        [UInt256.ofNat 5037,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 0x136c 5037
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 3455 .JUMPDEST)
    (blockOf _ (pcFactG input 3455 0x13ad [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 0x13ad [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 3456 .POP)
    (blockOf _ (pcFactG input 3456 0x13ae [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 0x13ae (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 3457 2 (UInt256.ofNat 5043))
    (blockOf _ (pcFactG input 3457 0x13af [] (by norm_num) pc2862)
      (stepG_push input 0x13af 2 (UInt256.ofNat 5043) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 3458 .POP)
    (blockOf _ (pcFactG input 3458 0x13b2 [UInt256.ofNat 5043] (by norm_num) pc2863)
      (stepG_pop input 0x13b2 (UInt256.ofNat 5043) [] (by simp) (by norm_num)))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

#print axioms gasSteps_checkEarly

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
