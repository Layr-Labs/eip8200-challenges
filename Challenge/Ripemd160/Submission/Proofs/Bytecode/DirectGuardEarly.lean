import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

pc 4958 is taken, the stub at pc 5023 drops the word and falls through to
the patterned guard at pc 5029.  The final one-byte dispatch pops the
already-consumed fall-through target instead of performing a redundant jump.
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
  have hcleanup : Decode.isValidJumpDest submissionBytecode 0x139f = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 3123 (by rfl)
  rw [show sizeMatched input = stG input 0x1336 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 0x13a5 [] from rfl]
  refine ?_
  have step0 := soundG (pushAt 3082 0 0)
    (blockOf _ (pcFactG input 3082 0x1336 [] (by norm_num) pc2819)
      (stepG_push0 input 0x1336 [] (by simp) (by norm_num)))
  have step1 := soundG (opAt 3083 .CALLDATALOAD)
    (blockOf _ (pcFactG input 3083 0x1337 [(⟨0⟩ : UInt256)] (by norm_num) pc2820)
      (stepG_calldataload input 0x1337 ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at step1
  have step2 := soundG (opAt 3084 (.Dup ⟨0, by decide⟩))
    (blockOf _ (pcFactG input 3084 0x1338 [referenceWord input] (by norm_num) pc2821)
      (stepG_dup1 input 0x1338 (referenceWord input) [] (by simp) (by norm_num)))
  have step3 := soundG (pushAt 3085 32 KnownInputData.fullWord)
    (blockOf _ (pcFactG input 3085 0x1339 [referenceWord input, referenceWord input]
        (by norm_num) pc2822)
      (stepG_push input 0x1339 32 KnownInputData.fullWord
        [referenceWord input, referenceWord input] (by simp) (by decide) (by decide)
        (by norm_num)))
  have step4 := soundG (opAt 3086 .XOR)
    (blockOf _ (pcFactG input 3086 0x135a
        [KnownInputData.fullWord, referenceWord input, referenceWord input]
        (by norm_num) pc2823)
      (stepG_xor input 0x135a KnownInputData.fullWord (referenceWord input)
        [referenceWord input] (by simp) (by norm_num)))
  have step5 := soundG (pushAt 3087 2 (UInt256.ofNat 5023))
    (blockOf _ (pcFactG input 3087 0x135b
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2824)
      (stepG_push input 0x135b 2 (UInt256.ofNat 5023)
        [UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step6 := soundG (opAt 3088 .JUMPI)
    (blockOf _ (pcFactG input 3088 0x135e
        [UInt256.ofNat 5023,
         UInt256.xor KnownInputData.fullWord (referenceWord input), referenceWord input]
        (by norm_num) pc2825)
      (stepG_jumpi_taken input 0x135e 5023
        (UInt256.xor KnownInputData.fullWord (referenceWord input))
        [referenceWord input] (by simp) (by norm_num) htrue hcleanup))
  have step7 := soundG (opAt 3123 .JUMPDEST)
    (blockOf _ (pcFactG input 3123 0x139f [referenceWord input] (by norm_num) pc2860)
      (stepG_jumpdest input 0x139f [referenceWord input] (by simp) (by norm_num)))
  have step8 := soundG (opAt 3124 .POP)
    (blockOf _ (pcFactG input 3124 0x13a0 [referenceWord input] (by norm_num) pc2861)
      (stepG_pop input 0x13a0 (referenceWord input) [] (by simp) (by norm_num)))
  have step9 := soundG (pushAt 3125 2 (UInt256.ofNat 5029))
    (blockOf _ (pcFactG input 3125 0x13a1 [] (by norm_num) pc2862)
      (stepG_push input 0x13a1 2 (UInt256.ofNat 5029) [] (by simp) (by decide)
        (by decide) (by norm_num)))
  have step10 := soundG (opAt 3126 .POP)
    (blockOf _ (pcFactG input 3126 0x13a4 [UInt256.ofNat 5029] (by norm_num) pc2863)
      (stepG_pop input 0x13a4 (UInt256.ofNat 5029) [] (by simp) (by norm_num)))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans (step9.trans step10)))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
