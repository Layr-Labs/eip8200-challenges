import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 190 is taken; the stub at pc 252 drops the word and falls through to the
guard at pc 254. The repeated-word construction is lifted as one block;
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0x109 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 156 (by rfl)
  rw [show sizeMatched input = stG input 0xbd [] from rfl,
    show PatternedScan.patternedEntry input = stG input 0x10b [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 111 0 0)
    (blockOf _ (pcFactG input 111 0xbd [] (by norm_num) pc2819)
      (stepG_push0 input 0xbd [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 112 .CALLDATALOAD)
    (blockOf _ (pcFactG input 112 0xbe [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 0xbe ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 113 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 113 0xbf [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 0xbf (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := RepeatedByteWordSite.gasSteps_fullWord
    (initialState submissionBytecode input 0) [referenceWord input, referenceWord input]
    (by simp) rfl rfl rfl deployAddress_not_precompile
  have step4 := soundG (opAt 120 .XOR)
    (blockOf _ (pcFactG input 120 0xc8
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 0xc8 KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 121 2 (UInt256.ofNat 265))
    (blockOf _ (pcFactG input 121 0xc9
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 0xc9 2 (UInt256.ofNat 265)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 122 .JUMPI)
    (blockOf _ (pcFactG input 122 0xcc
        [UInt256.ofNat 265,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 0xcc 265
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 156 .JUMPDEST)
    (blockOf _ (pcFactG input 156 0x109 [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 0x109 [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 157 .POP)
    (blockOf _ (pcFactG input 157 0x10a [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 0x10a (referenceWord input) [] (by simp) (by norm_num)))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans (step5.trans (step6.trans (step7.trans (step8))))))))

#print axioms gasSteps_checkEarly

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
