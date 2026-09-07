import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 4862 is taken, the stub at pc 4927 drops the word and falls through to the
guard at pc 4933. POP consumes the old jump target for six fewer gas.
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0x133f = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3023 (by rfl)
  rw [show sizeMatched input = stG input 0x12d6 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 0x1345 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 2982 0 0)
    (blockOf _ (pcFactG input 2982 0x12d6 [] (by norm_num) pc2819)
      (stepG_push0 input 0x12d6 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 2983 .CALLDATALOAD)
    (blockOf _ (pcFactG input 2983 0x12d7 [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 0x12d7 ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 2984 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 2984 0x12d8 [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 0x12d8 (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := soundG (pushAt 2985 32 KnownInputData.fullWord)
    (blockOf _ (pcFactG input 2985 0x12d9 [referenceWord input, referenceWord input]
        (by norm_num) pc2822)
      (stepG_push input 0x12d9 32 KnownInputData.fullWord
        [referenceWord input, referenceWord input] (by simp) (by decide) (by decide)
        (by norm_num)))
  have step4 := soundG (opAt 2986 .XOR)
    (blockOf _ (pcFactG input 2986 0x12fa
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 0x12fa KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 2987 2 (UInt256.ofNat 4927))
    (blockOf _ (pcFactG input 2987 0x12fb
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 0x12fb 2 (UInt256.ofNat 4927)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 2988 .JUMPI)
    (blockOf _ (pcFactG input 2988 0x12fe
        [UInt256.ofNat 4927,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 0x12fe 4927
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 3023 .JUMPDEST)
    (blockOf _ (pcFactG input 3023 0x133f [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 0x133f [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 3024 .POP)
    (blockOf _ (pcFactG input 3024 0x1340 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 0x1340 (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 3025 2 (UInt256.ofNat 4933))
    (blockOf _ (pcFactG input 3025 0x1341 [] (by norm_num) pc2862)
      (stepG_push input 0x1341 2 (UInt256.ofNat 4933) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 3026 .POP)
    (blockOf _ (pcFactG input 3026 0x1344 [UInt256.ofNat 4933] (by norm_num) pc2863)
      (stepG_pop input 0x1344 (UInt256.ofNat 4933) [] (by simp) (by norm_num)))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
