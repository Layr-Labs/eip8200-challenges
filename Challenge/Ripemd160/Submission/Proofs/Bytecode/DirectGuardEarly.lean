import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The jump into the patterned guard

The first word differs from the 1000-a word. The repeated-word producer runs
and XOR consumes the calldata reference. The taken branch enters the patterned
guard with an empty stack.
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

private theorem pc_e23 : Artifact.submissionArtifact.instructionPC 23 = 35 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_e24 : Artifact.submissionArtifact.instructionPC 24 = 36 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_e25 : Artifact.submissionArtifact.instructionPC 25 = 37 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_e26 : Artifact.submissionArtifact.instructionPC 26 = 38 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc_e27 : Artifact.submissionArtifact.instructionPC 27 = 41 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

/-- A first word other than the repeated `0x61` word jumps to the patterned guard. -/
def gasSteps_checkEarly (input : ByteArray)
    (href : referenceWord input ≠ KnownInputData.fullWord) :
    GasSteps (sizeMatched input) (stG input 4803 []) := by
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
  rw [show sizeMatched input = stG input 27 [] from rfl]
  have step0 := RepeatedByteWordSite.gasSteps_fullWord
    (initialState submissionBytecode input 0) []
    (by simp) rfl rfl rfl deployAddress_not_precompile
  have step1 := soundG (pushAt 23 0 0)
    (blockOf _ (pcFactG input 23 35 [KnownInputData.fullWord] (by norm_num) pc_e23)
      (stepG_push0 input 35 [KnownInputData.fullWord] (by simp) (by norm_num)))
  have step2 := soundG (opAt 24 .CALLDATALOAD)
    (blockOf _ (pcFactG input 24 36 [(⟨0⟩ : UInt256), KnownInputData.fullWord]
      (by norm_num) pc_e24)
      (stepG_calldataload input 36 ⟨0⟩ [KnownInputData.fullWord] (by simp) (by norm_num)))
  rw [refW_eq] at step2
  have step3 := soundG (opAt 25 .XOR)
    (blockOf _ (pcFactG input 25 37 [referenceWord input, KnownInputData.fullWord]
      (by norm_num) pc_e25)
      (stepG_xor input 37 (referenceWord input) KnownInputData.fullWord [] (by simp) (by norm_num)))
  have step4 := soundG (pushAt 26 2 (UInt256.ofNat 4803))
    (blockOf _ (pcFactG input 26 38 [UInt256.xor (referenceWord input) KnownInputData.fullWord]
      (by norm_num) pc_e26)
      (stepG_push input 38 2 (UInt256.ofNat 4803)
        [UInt256.xor (referenceWord input) KnownInputData.fullWord]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step5 := soundG (opAt 27 .JUMPI)
    (blockOf _ (pcFactG input 27 41 [4803, UInt256.xor (referenceWord input) KnownInputData.fullWord]
      (by norm_num) pc_e27)
      (stepG_jumpi_taken input 41 4803 (UInt256.xor (referenceWord input) KnownInputData.fullWord)
        [] (by simp) (by norm_num) htrue guard_dest))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans step5))))

#print axioms gasSteps_checkEarly

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
