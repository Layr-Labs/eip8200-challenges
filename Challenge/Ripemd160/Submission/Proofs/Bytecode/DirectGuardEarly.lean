import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word of the calldata is not the 1000-a word, so the `JUMPI` at
pc 5146 is taken, the stub at pc 5208 drops the word and falls through to the appended
guard at pc 5214. The repeated-word construction is lifted as one block;
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0xfe = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 148 (by rfl)
  rw [show sizeMatched input = stG input 0xb1 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 0x100 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 103 0 0)
    (blockOf _ (pcFactG input 103 0xb1 [] (by norm_num) pc2819)
      (stepG_push0 input 0xb1 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 104 .CALLDATALOAD)
    (blockOf _ (pcFactG input 104 0xb2 [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 0xb2 ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 105 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 105 0xb3 [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 0xb3 (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := RepeatedByteWordSite.gasSteps_fullWord
    (initialState submissionBytecode input 0) [referenceWord input, referenceWord input]
    (by simp) rfl rfl rfl deployAddress_not_precompile
  have step4 := soundG (opAt 112 .XOR)
    (blockOf _ (pcFactG input 112 0xbc
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 0xbc KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 113 2 (UInt256.ofNat 254))
    (blockOf _ (pcFactG input 113 0xbd
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 0xbd 2 (UInt256.ofNat 254)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 114 .JUMPI)
    (blockOf _ (pcFactG input 114 0xc0
        [UInt256.ofNat 254,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 0xc0 254
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 148 .JUMPDEST)
    (blockOf _ (pcFactG input 148 0xfe [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 0xfe [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 149 .POP)
    (blockOf _ (pcFactG input 149 0xff [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 0xff (referenceWord input) [] (by simp) (by norm_num)))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans (step5.trans (step6.trans (step7.trans (step8))))))))

#print axioms gasSteps_checkEarly

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
