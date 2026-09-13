import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The fall-through into the patterned guard

The first word differs from the 1000-a word. The repeated-word producer runs
and XOR consumes the calldata reference. The taken branch enters the scanner
with an empty stack.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

private theorem refW_eq (input : ByteArray) :
    MachineState.readWord input ((⟨0⟩ : UInt256).toNat) = referenceWord input := rfl

private theorem stepG_dup2 (input : ByteArray) (pc : Nat) (a b : UInt256)
    (rest : List UInt256) (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.DataStepper.runInstr (.op (.Dup ⟨1, by decide⟩))
        (stG input pc (a :: b :: rest)) =
      some (stG input (pc + 1) (b :: a :: b :: rest)) := by
  unfold Challenge.EvmProof.DataStepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stG_stack]
  show (match some b with
    | some value => some { stG input pc (a :: b :: rest) with
        stack := value :: (stG input pc (a :: b :: rest)).stack
        pc := (stG input pc (a :: b :: rest)).pc.succ }
    | none => none) = _
  simp only [stG, Challenge.EvmProof.Word.succ_ofNat hpc]

def gasSteps_checkEarly (input : ByteArray)
    (href : referenceWord input ≠ KnownInputData.fullWord) :
    GasSteps (sizeMatched input) (PatternedScan.patternedEntry input) := by
  have hxor : UInt256.xor (referenceWord input) KnownInputData.fullWord ≠ 0 := by
    intro hz
    exact href ((KnownInputLogic.wordXor_eq_zero_iff
      (referenceWord input) KnownInputData.fullWord).1 hz)
  have htrue : UInt256.isTrue
      (UInt256.xor (referenceWord input) KnownInputData.fullWord) = true := by
    have h : UInt256.isTrue (UInt256.xor (referenceWord input) KnownInputData.fullWord) := by
      intro hnat
      apply hxor
      apply Challenge.EvmProof.Word.word_ext
      exact hnat
    simpa using h
  have hcleanup : Decode.isValidJumpDest submissionBytecode 115 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 71 (by rfl)
  rw [show sizeMatched input = stG input 30 [] from rfl,
    show PatternedScan.patternedEntry input = stG input 116 [] from rfl]
  have step0 := RepeatedByteWordSite.gasSteps_fullWord
    (initialState submissionBytecode input 0) []
    (by simp) rfl rfl rfl deployAddress_not_precompile
  have step1 := soundG (pushAt 25 0 0)
    (blockOf _ (pcFactG input 25 38 [KnownInputData.fullWord] (by norm_num) producerEndPC)
      (stepG_push0 input 38 [KnownInputData.fullWord] (by simp) (by norm_num)))
  have step2 := soundG (opAt 26 .CALLDATALOAD)
    (blockOf _ (pcFactG input 26 39 [(⟨0⟩ : UInt256), KnownInputData.fullWord]
      (by norm_num) earlyWordLoadPC)
      (stepG_calldataload input 39 ⟨0⟩ [KnownInputData.fullWord] (by simp) (by norm_num)))
  rw [refW_eq] at step2
  have step3 := soundG (opAt 27 .XOR)
    (blockOf _ (pcFactG input 27 40 [referenceWord input, KnownInputData.fullWord]
      (by norm_num) pc2823)
      (stepG_xor input 40 (referenceWord input) KnownInputData.fullWord [] (by simp) (by norm_num)))
  have step4 := soundG (pushAt 28 1 (UInt256.ofNat 115))
    (blockOf _ (pcFactG input 28 41 [UInt256.xor (referenceWord input) KnownInputData.fullWord]
      (by norm_num) pc2824)
      (stepG_push input 41 1 (UInt256.ofNat 115)
        [UInt256.xor (referenceWord input) KnownInputData.fullWord]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step5 := soundG (opAt 29 .JUMPI)
    (blockOf _ (pcFactG input 29 43 [115, UInt256.xor (referenceWord input) KnownInputData.fullWord]
      (by norm_num) pc2825)
      (stepG_jumpi_taken input 43 115 (UInt256.xor (referenceWord input) KnownInputData.fullWord)
        [] (by simp) (by norm_num) htrue hcleanup))
  have step6 := soundG (opAt 71 .JUMPDEST)
    (blockOf _ (pcFactG input 71 115 [] (by norm_num) pc2860)
      (stepG_jumpdest input 115 [] (by simp) (by norm_num)))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans (step5.trans step6)))))

#print axioms gasSteps_checkEarly

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
