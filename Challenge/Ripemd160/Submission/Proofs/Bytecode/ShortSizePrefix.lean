import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def shortSizePrefix : List Located :=
  [opAt 0 .CALLDATASIZE, pushAt 1 1 255, opAt 2 .GT, pushAt 3 2 4842]

def shortSizePath : List Located := shortSizePrefix ++ [opAt 4 .JUMPI]

def sizeDispatchPath (input : ByteArray) : List Located :=
  if input.size < 255 then shortSizePath else shortSizePath ++ sizePath

def shortSizeCondition (input : ByteArray) : UInt256 :=
  UInt256.gt (UInt256.ofNat 255) (UInt256.ofNat input.size)

private theorem prefix_pc4 : Artifact.submissionArtifact.instructionPC 4 = 7 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem short_dest : Decode.isValidJumpDest submissionBytecode 4842 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3833 = 4842 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3839 (by rfl)
  rwa [hpc] at h

private theorem run_short_prefix (input : ByteArray) :
    run shortSizePrefix (Execution.atPC input 0) =
      some (PatternedScan.stS input 7 [4842, shortSizeCondition input]) := by
  have pc0 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have pc1 : Artifact.submissionArtifact.instructionPC 1 = 1 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have pc2 : Artifact.submissionArtifact.instructionPC 2 = 3 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have pc3 : Artifact.submissionArtifact.instructionPC 3 = 4 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  simp (config := { maxSteps := 400000 })
    [shortSizePrefix, shortSizeCondition, opAt, pushAt, wfOp,
     Execution.atPC, PatternedScan.stS, initialState,
     pc0, pc1, pc2, pc3,
     Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
     Word.literal_eq_ofNat, Word.succ_ofNat_mod,
     Word.ofNat_add_mod, Word.word_toNat_ofNat]

private theorem short_condition_one (input : ByteArray) (hsmall : input.size < 255) :
    shortSizeCondition input = UInt256.ofNat 1 := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hsmall (by norm_num)
  have hmod : input.size % UInt256.size = input.size := by
    unfold UInt256.size
    exact Nat.mod_eq_of_lt hlt
  unfold shortSizeCondition UInt256.gt
  simp only [UInt256.toNat, UInt256.ofNat, Fin.val_ofNat]
  rw [hmod]
  have h256 : 255 % UInt256.size = 255 := by norm_num [UInt256.size]
  simp [h256, hsmall]

private theorem short_condition_zero (input : ByteArray) (hfit : CalldataFits input)
    (hlarge : ¬ input.size < 255) :
    shortSizeCondition input = UInt256.ofNat 0 := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hmod : input.size % UInt256.size = input.size := by
    unfold UInt256.size
    exact Nat.mod_eq_of_lt hlt
  unfold shortSizeCondition UInt256.gt
  simp only [UInt256.toNat, UInt256.ofNat, Fin.val_ofNat]
  rw [hmod]
  have h256 : 255 % UInt256.size = 255 := by norm_num [UInt256.size]
  simp [h256, hlarge]

theorem run_short_size_taken (input : ByteArray) (hsmall : input.size < 255) :
    run shortSizePath (Execution.atPC input 0) = some (atPC input 4842) := by
  have hp := run_short_prefix input
  rw [short_condition_one input hsmall] at hp
  have hj : run [opAt 4 .JUMPI]
      (PatternedScan.stS input 7 [4842, UInt256.ofNat 1]) =
      some (PatternedScan.stS input 4842 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 4 7 _ (by norm_num) prefix_pc4)
      (PatternedScan.stepS_jumpi_taken input 7 4842 4842 (UInt256.ofNat 1) []
        (by simp) (by norm_num) rfl (by decide) short_dest)
  exact Stepper.runLocatedBlock_append shortSizePrefix [opAt 4 .JUMPI]
    _ _ _ hp rfl hj

theorem run_short_size_fall (input : ByteArray) (hfit : CalldataFits input)
    (hlarge : ¬ input.size < 255) :
    run shortSizePath (Execution.atPC input 0) = some (Execution.atPC input 8) := by
  have hp := run_short_prefix input
  rw [short_condition_zero input hfit hlarge] at hp
  have hj : run [opAt 4 .JUMPI]
      (PatternedScan.stS input 7 [4842, UInt256.ofNat 0]) =
      some (PatternedScan.stS input 8 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 4 7 _ (by norm_num) prefix_pc4)
      (PatternedScan.stepS_jumpi_fall input 7 4842 (UInt256.ofNat 0) []
        (by simp) (by norm_num) (by decide))
  exact Stepper.runLocatedBlock_append shortSizePrefix [opAt 4 .JUMPI]
    _ _ _ hp rfl hj

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
