import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 5055 is taken, the stub at pc 5120 drops the word and jumps to the appended
guard at pc 174.  The eleven instructions are taken one at a time.
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0x6f = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 45 (by rfl)
  have hblock : Decode.isValidJumpDest submissionBytecode 0x74 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 49 (by rfl)
  rw [show sizeMatched input = stG input 0x9 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 0x74 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 5 0 0)
    (blockOf _ (pcFactG input 5 0x9 [] (by norm_num) pc2819)
      (stepG_push0 input 0x9 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 6 .CALLDATALOAD)
    (blockOf _ (pcFactG input 6 0xa [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 0xa ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 7 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 7 0xb [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 0xb (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := soundG (pushAt 8 32 KnownInputData.fullWord)
    (blockOf _ (pcFactG input 8 0xc [referenceWord input, referenceWord input]
        (by norm_num) pc2822)
      (stepG_push input 0xc 32 KnownInputData.fullWord
        [referenceWord input, referenceWord input] (by simp) (by decide) (by decide)
        (by norm_num)))
  have step4 := soundG (opAt 9 .XOR)
    (blockOf _ (pcFactG input 9 0x2d
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 0x2d KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 10 1 (UInt256.ofNat 111))
    (blockOf _ (pcFactG input 10 0x2e
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 0x2e 1 (UInt256.ofNat 111)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 11 .JUMPI)
    (blockOf _ (pcFactG input 11 0x30
        [UInt256.ofNat 111,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 0x30 111
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 45 .JUMPDEST)
    (blockOf _ (pcFactG input 45 0x6f [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 0x6f [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 46 .POP)
    (blockOf _ (pcFactG input 46 0x70 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 0x70 (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 47 1 (UInt256.ofNat 116))
    (blockOf _ (pcFactG input 47 0x71 [] (by norm_num) pc2862)
      (stepG_push input 0x71 1 (UInt256.ofNat 116) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 48 .JUMP)
    (blockOf _ (pcFactG input 48 0x73 [UInt256.ofNat 116] (by norm_num) pc2863)
      (stepG_jump input 0x73 116 [] (by simp) (by norm_num) hblock))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
