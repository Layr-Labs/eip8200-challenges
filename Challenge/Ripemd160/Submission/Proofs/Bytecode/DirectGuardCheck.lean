import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The first-word check that chooses between the two guards. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

theorem run_checkEntry (input : ByteArray)
    (href : referenceWord input = KnownInputData.fullWord) :
    run checkEntryPath (sizeMatched input) = some (loopState input 0) := by
  have hpc3278 : Artifact.submissionArtifact.instructionPC 115 = 194 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hpc3279 : Artifact.submissionArtifact.instructionPC 116 = 195 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hpc3280 : Artifact.submissionArtifact.instructionPC 117 = 196 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hpc3281 : Artifact.submissionArtifact.instructionPC 118 = 197 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hpc3282 : Artifact.submissionArtifact.instructionPC 119 = 199 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hzero : UInt256.xor KnownInputData.fullWord (referenceWord input) = 0 := by
    exact (KnownInputLogic.wordXor_eq_zero_iff
      KnownInputData.fullWord (referenceWord input)).2 href.symm
  have hfalse : ¬ UInt256.isTrue
      (UInt256.xor KnownInputData.fullWord (referenceWord input)) := by
    rw [hzero]
    decide
  have hcond : ¬ UInt256.isTrue
      (UInt256.xor KnownInputData.fullWord (MachineState.readWord input 0)) := by
    simpa only [referenceWord] using hfalse
  have hstack : UInt256.xor KnownInputData.fullWord
      (MachineState.readWord input 0) =
      UInt256.xor (MachineState.readWord input 0) KnownInputData.fullWord :=
    BooleanSelect.xor_comm _ _
  have hcondStack : ¬ UInt256.isTrue
      (UInt256.xor (MachineState.readWord input 0) KnownInputData.fullWord) := by
    rw [← hstack]
    exact hcond
  have hstackZero :
      UInt256.xor (MachineState.readWord input 0) KnownInputData.fullWord =
        UInt256.ofNat 0 := by
    rw [← hstack, show UInt256.ofNat 0 = 0 by rfl]
    simpa only [referenceWord] using hzero
  have hzeroFalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have hpushzero : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hfullWordMul : UInt256.mul (UInt256.ofNat 97) PatternedSwar.M =
      KnownInputData.fullWord := RepeatedByteWord.ascii_a
  simp (config := { maxSteps := 1000000 })
    [hpc3278, hpc3279, hpc3280, hpc3281, hpc3282, hpushzero, hfullWordMul, CompactGuardConstants.repeated_one_ofNat, RepeatedByteWord.ascii_a, checkEntryPath, opAt, pushAt, wfOp, sizeMatched, atPC, loopState,
    loopAcc, referenceWord, href, hzero, hfalse, hcond, hstack, hcondStack,
    hstackZero, hzeroFalse,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

#print axioms run_checkEntry

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
