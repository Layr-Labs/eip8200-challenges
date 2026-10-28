import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Jumpdest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Hop of the pad-only copy past its word-0 folds

The folds lengthen paired rounds 0 to 73.  Paired rounds 74 to 79, the unpack and the tail
moved past the end of the old image, so round 73 ends at 7916 with a hop to the marker at
10024 and the copy resumes at 10025.  Every pc from 8051 on keeps its old position.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FoldHop
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate HoistedInherited.Jumpdest

private theorem valid_at (s : State) (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (index pc : Nat) (hpc : HoistedInherited.Artifact.submissionArtifact.instructionPC index = pc)
    (hj : HoistedInherited.Artifact.submissionArtifact.instructions[index]? = some (.op .JUMPDEST)) :
    Decode.isValidJumpDest s.executionEnv.code pc = true := by
  have h := HoistedInherited.Artifact.submissionArtifact.isValidJumpDest_index index hj
  rw [hpc] at h
  rw [hcode]
  exact h

theorem valid_10024 (s : State) (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 10024 = true :=
  valid_at s hcode 6824 10024 (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide) (by rfl)

theorem hop_advances (target : Nat) (h : (hopTemplate target).dropLast.all PadLift.advancesCheck = true) :
    ∀ instruction ∈ (hopTemplate target).dropLast, PadLift.Advances instruction :=
  PadLift.advancesAll_sound _ h

theorem hop_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 5946).take (hopTemplate 10024).length = hopTemplate 10024 := by rfl

def hopSite : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (hopTemplate 10024) :=
  StackSiteBuilder.ofSlice (hopTemplate 10024) 5946 hop_slice
    (by change 5946 + (hopTemplate 10024).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := hopTemplate 10024) (by decide))
    (by decide)

theorem hop_pc : hopSite.startPC = UInt256.ofNat 7916 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 5946) = UInt256.ofNat 7916
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem mark_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 6824).take markTemplate.length = markTemplate := by rfl

def markResumeSite : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka markTemplate :=
  markSite 6824 mark_slice
    (by rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)

theorem mark_pc : markResumeSite.startPC = UInt256.ofNat 10024 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6824) = UInt256.ofNat 10024
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- Leave paired round 73 at 7916 and resume the copy past the marker at 10024. -/
def gasSteps_hop (s : State) (st : List UInt256) (hstack : st.length ≤ 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 7916, stack := st}
      {s with pc := UInt256.ofNat 10025, stack := st} := by
  have g1 : GasSteps {s with pc := UInt256.ofNat 7916, stack := st}
      {s with pc := UInt256.ofNat 10024, stack := st} :=
    PadLift.gasSteps_of_raw hopSite _ _ hcode hfork hrun hnp hop_pc.symm (hop_advances 10024 (by decide))
      (run_hop s _ 10024 st hstack hrun (by decide) (valid_10024 s hcode))
  have hraw := run_mark s (UInt256.ofNat 10024) st hstack hrun
  have hend : pcAfter (UInt256.ofNat 10024) markTemplate = UInt256.ofNat 10025 := by decide
  rw [hend] at hraw
  have g2 := DenseScheduleLift.gasSteps_of_raw markResumeSite {s with pc := UInt256.ofNat 10024, stack := st}
    {s with pc := UInt256.ofNat 10025, stack := st} hcode hfork hrun hnp mark_pc.symm mark_advances hraw
  exact g1.trans g2

#print axioms gasSteps_hop
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FoldHop
