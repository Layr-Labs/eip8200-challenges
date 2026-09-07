import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 5079 is taken, the stub at pc 5144 drops the word and jumps to the appended
guard at pc 5150. The repeated-word construction is lifted as one block;
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0x1418 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3320 (by rfl)
  have hblock : Decode.isValidJumpDest submissionBytecode 0x141e = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3324 (by rfl)
  rw [show sizeMatched input = stG input 0x13c8 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 0x141e [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 3274 0 0)
    (blockOf _ (pcFactG input 3274 0x13c8 [] (by norm_num) pc2819)
      (stepG_push0 input 0x13c8 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 3275 .CALLDATALOAD)
    (blockOf _ (pcFactG input 3275 0x13c9 [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 0x13c9 ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 3276 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 3276 0x13ca [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 0x13ca (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := RepeatedByteWordSite.gasSteps_fullWord
    (initialState submissionBytecode input 0) [referenceWord input, referenceWord input]
    (by simp) rfl rfl rfl deployAddress_not_precompile
  have step4 := soundG (opAt 3283 .XOR)
    (blockOf _ (pcFactG input 3283 0x13d3
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 0x13d3 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 3284 2 (UInt256.ofNat 5144))
    (blockOf _ (pcFactG input 3284 0x13d4
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 0x13d4 2 (UInt256.ofNat 5144)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 3285 .JUMPI)
    (blockOf _ (pcFactG input 3285 0x13d7
        [UInt256.ofNat 5144,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 0x13d7 5144
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 3320 .JUMPDEST)
    (blockOf _ (pcFactG input 3320 0x1418 [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 0x1418 [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 3321 .POP)
    (blockOf _ (pcFactG input 3321 0x1419 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 0x1419 (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 3322 2 (UInt256.ofNat 5150))
    (blockOf _ (pcFactG input 3322 0x141a [] (by norm_num) pc2862)
      (stepG_push input 0x141a 2 (UInt256.ofNat 5150) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 3323 .JUMP)
    (blockOf _ (pcFactG input 3323 0x141d [UInt256.ofNat 5150] (by norm_num) pc2863)
      (stepG_jump input 0x141d 5150 [] (by simp) (by norm_num) hblock))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

#print axioms gasSteps_checkEarly

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
