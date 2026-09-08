import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 68 is taken, the stub at pc 131 drops the word and jumps to the appended
guard at pc 136.  The eleven instructions are taken one at a time.
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0x83 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 60 (by rfl)
  have hblock : Decode.isValidJumpDest submissionBytecode 0x88 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 64 (by rfl)
  rw [show sizeMatched input = stG input 0x1d [] from rfl,
    show PatternedScan.patternedEntry input = stG input 0x88 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 20 0 0)
    (blockOf _ (pcFactG input 20 0x1d [] (by norm_num) pc2819)
      (stepG_push0 input 0x1d [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 21 .CALLDATALOAD)
    (blockOf _ (pcFactG input 21 0x1e [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 0x1e ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 22 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 22 0x1f [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 0x1f (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := soundG (pushAt 23 32 KnownInputData.fullWord)
    (blockOf _ (pcFactG input 23 0x20 [referenceWord input, referenceWord input]
        (by norm_num) pc2822)
      (stepG_push input 0x20 32 KnownInputData.fullWord
        [referenceWord input, referenceWord input] (by simp) (by decide) (by decide)
        (by norm_num)))
  have step4 := soundG (opAt 24 .XOR)
    (blockOf _ (pcFactG input 24 0x41
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 0x41 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 25 1 (UInt256.ofNat 131))
    (blockOf _ (pcFactG input 25 0x42
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 0x42 1 (UInt256.ofNat 131)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 26 .JUMPI)
    (blockOf _ (pcFactG input 26 0x44
        [UInt256.ofNat 131,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 0x44 131
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 60 .JUMPDEST)
    (blockOf _ (pcFactG input 60 0x83 [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 0x83 [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 61 .POP)
    (blockOf _ (pcFactG input 61 0x84 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 0x84 (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 62 1 (UInt256.ofNat 136))
    (blockOf _ (pcFactG input 62 0x85 [] (by norm_num) pc2862)
      (stepG_push input 0x85 1 (UInt256.ofNat 136) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 63 .JUMP)
    (blockOf _ (pcFactG input 63 0x87 [UInt256.ofNat 136] (by norm_num) pc2863)
      (stepG_jump input 0x87 136 [] (by simp) (by norm_num) hblock))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
