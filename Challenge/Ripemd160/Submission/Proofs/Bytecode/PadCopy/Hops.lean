import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Jumpdest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Control transfers of the specialised pad-only prefix

The prefix occupies two padding windows: rounds up to 3 end at byte 6491 with a
hop to the second window's marker at 7046, and round 12 ends at 7375 with a hop
to the generic compressor's marker at 1557.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Hops
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

theorem valid_7046 (s : State) (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 7046 = true :=
  valid_at s hcode 4252 7046 (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide) (by rfl)

theorem valid_1557 (s : State) (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 1557 = true :=
  valid_at s hcode 946 1557 (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide) (by rfl)

theorem hop_advances (target : Nat) (h : (hopTemplate target).dropLast.all PadLift.advancesCheck = true) :
    ∀ instruction ∈ (hopTemplate target).dropLast, PadLift.Advances instruction :=
  PadLift.advancesAll_sound _ h

/-! ## First window → second window -/

theorem hopA_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 4097).take (hopTemplate 7046).length = hopTemplate 7046 := by rfl

def hopASite : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (hopTemplate 7046) :=
  StackSiteBuilder.ofSlice (hopTemplate 7046) 4097 hopA_slice
    (by change 4097 + (hopTemplate 7046).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := hopTemplate 7046) (by decide))
    (by decide)

theorem hopA_pc : hopASite.startPC = UInt256.ofNat 6491 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 4097) = UInt256.ofNat 6491
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem markB_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 4252).take markTemplate.length = markTemplate := by rfl

def markBSite : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka markTemplate :=
  markSite 4252 markB_slice
    (by rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)

theorem markB_pc : markBSite.startPC = UInt256.ofNat 7046 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 4252) = UInt256.ofNat 7046
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- Leave the first window at 6491 and enter the second window past its marker. -/
def gasSteps_window (s : State) (st : List UInt256) (hstack : st.length ≤ 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 6491, stack := st}
      {s with pc := UInt256.ofNat 7047, stack := st} := by
  have g1 : GasSteps {s with pc := UInt256.ofNat 6491, stack := st}
      {s with pc := UInt256.ofNat 7046, stack := st} :=
    PadLift.gasSteps_of_raw hopASite _ _ hcode hfork hrun hnp hopA_pc.symm (hop_advances 7046 (by decide))
      (run_hop s _ 7046 st hstack hrun (by decide) (valid_7046 s hcode))
  have hraw := run_mark s (UInt256.ofNat 7046) st hstack hrun
  have hend : pcAfter (UInt256.ofNat 7046) markTemplate = UInt256.ofNat 7047 := by decide
  rw [hend] at hraw
  have g2 := DenseScheduleLift.gasSteps_of_raw markBSite {s with pc := UInt256.ofNat 7046, stack := st}
    {s with pc := UInt256.ofNat 7047, stack := st} hcode hfork hrun hnp markB_pc.symm mark_advances hraw
  exact g1.trans g2

/-! ## Second window → generic round 13 -/

theorem hopB_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 4546).take (hopTemplate 1557).length = hopTemplate 1557 := by rfl

def hopBSite : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (hopTemplate 1557) :=
  StackSiteBuilder.ofSlice (hopTemplate 1557) 4546 hopB_slice
    (by change 4546 + (hopTemplate 1557).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := hopTemplate 1557) (by decide))
    (by decide)

theorem hopB_pc : hopBSite.startPC = UInt256.ofNat 7375 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 4546) = UInt256.ofNat 7375
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- Leave the second window and resume the generic compressor past its marker. -/
def gasSteps_rejoin (s : State) (st : List UInt256) (hstack : st.length ≤ 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 7375, stack := st}
      {s with pc := UInt256.ofNat 1558, stack := st} := by
  have g1 : GasSteps {s with pc := UInt256.ofNat 7375, stack := st}
      {s with pc := UInt256.ofNat 1557, stack := st} :=
    PadLift.gasSteps_of_raw hopBSite _ _ hcode hfork hrun hnp hopB_pc.symm (hop_advances 1557 (by decide))
      (run_hop s _ 1557 st hstack hrun (by decide) (valid_1557 s hcode))
  exact g1.trans (gasSteps_core s st hstack hrun hcode hfork hnp)

#print axioms gasSteps_window
#print axioms gasSteps_rejoin
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Hops
