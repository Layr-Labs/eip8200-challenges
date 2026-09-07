import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 5068 is taken, the stub at pc 5133 drops the word and falls through to the appended
guard at pc 5139. The repeated-word construction is lifted as one block;
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0x140d = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3653 (by rfl)
  rw [show sizeMatched input = stG input 0x13bd [] from rfl,
    show PatternedScan.patternedEntry input = stG input 0x1413 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 3607 0 0)
    (blockOf _ (pcFactG input 3607 0x13bd [] (by norm_num) pc2819)
      (stepG_push0 input 0x13bd [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 3608 .CALLDATALOAD)
    (blockOf _ (pcFactG input 3608 0x13be [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 0x13be ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 3609 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 3609 0x13bf [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 0x13bf (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := RepeatedByteWordSite.gasSteps_fullWord
    (initialState submissionBytecode input 0) [referenceWord input, referenceWord input]
    (by simp) rfl rfl rfl deployAddress_not_precompile
  have step4 := soundG (opAt 3616 .XOR)
    (blockOf _ (pcFactG input 3616 0x13c8
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 0x13c8 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 3617 2 (UInt256.ofNat 5133))
    (blockOf _ (pcFactG input 3617 0x13c9
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 0x13c9 2 (UInt256.ofNat 5133)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 3618 .JUMPI)
    (blockOf _ (pcFactG input 3618 0x13cc
        [UInt256.ofNat 5133,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 0x13cc 5133
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 3653 .JUMPDEST)
    (blockOf _ (pcFactG input 3653 0x140d [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 0x140d [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 3654 .POP)
    (blockOf _ (pcFactG input 3654 0x140e [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 0x140e (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 3655 2 (UInt256.ofNat 5139))
    (blockOf _ (pcFactG input 3655 0x140f [] (by norm_num) pc2862)
      (stepG_push input 0x140f 2 (UInt256.ofNat 5139) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 3656 .POP)
    (blockOf _ (pcFactG input 3656 0x1412 [UInt256.ofNat 5139] (by norm_num) pc2863)
      (stepG_pop input 0x1412 (UInt256.ofNat 5139) [] (by simp) (by norm_num)))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

#print axioms gasSteps_checkEarly

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
