import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStartRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentLoopSites
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStart
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PersistentStartRaw

theorem initial_slice :
    (Artifact.submissionArtifact.instructions.drop 221).take initialTemplate.length = initialTemplate := by rfl

def initialSite : GenericRoundSite Artifact.submissionArtifact .Osaka initialTemplate :=
  StackSiteBuilder.ofSlice initialTemplate 221 initial_slice
    (by change 221 + initialTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    Artifact.code_size_lt
    (StackRoundData.templateWellFormed_mem (instructions := initialTemplate) (by decide))
    (by decide)

theorem initial_pc : initialSite.startPC = UInt256.ofNat 335 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 221) = UInt256.ofNat 335
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def testCode : List Instr := testTemplate 504

theorem test_slice :
    (Artifact.submissionArtifact.instructions.drop 226).take testCode.length = testCode := by rfl

def testSite : GenericRoundSite Artifact.submissionArtifact .Osaka testCode :=
  StackSiteBuilder.ofSlice testCode 226 test_slice
    (by change 226 + testCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    Artifact.code_size_lt
    (StackRoundData.templateWellFormed_mem (instructions := testCode) (by decide))
    (by decide)

theorem test_pc : testSite.startPC = UInt256.ofNat 360 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 226) = UInt256.ofNat 360
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 504).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 307 = 504 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 307 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 504 = true
  rw [hcode]
  exact h

def gasSteps_initial (s : State) (off limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 335, stack := off :: limit :: rho}
      {s with pc := UInt256.ofNat 360, stack := PersistentFrame.frame StackRunBridge.initialHashState off limit rho} := by
  apply PadLift.gasSteps_of_raw initialSite {s with pc := UInt256.ofNat 335, stack := off :: limit :: rho} _
    hcode hfork hrun hnp initial_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · have hraw := run_initial s (UInt256.ofNat 335) off limit rho (by omega) hrun
    have hp : pcAfter (UInt256.ofNat 335) initialTemplate = UInt256.ofNat 360 := by decide
    rw [hp] at hraw
    exact hraw

def gasSteps_positive (s : State) (off limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2^256) (hpos : 0 < s.executionEnv.calldata.size)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 335, stack := off :: limit :: rho}
      {s with pc := UInt256.ofNat 505, stack := PersistentFrame.frame StackRunBridge.initialHashState off limit rho} := by
  let frame := PersistentFrame.frame StackRunBridge.initialHashState off limit rho
  have gi := gasSteps_initial s off limit rho hstack hrun hcode hfork hnp
  have gt : GasSteps {s with pc := UInt256.ofNat 360, stack := frame}
      {s with pc := UInt256.ofNat 504, stack := frame} := by
    apply PadLift.gasSteps_of_raw testSite {s with pc := UInt256.ofNat 360, stack := frame} _
      hcode hfork hrun hnp test_pc.symm
    · apply PadLift.advancesAll_sound
      decide
    · exact run_positive s (UInt256.ofNat 360) frame 504
        (by simp [frame, PersistentFrame.frame]; omega) hrun hfit hpos (valid_loop s hcode)
  exact gi.trans (gt.trans (PersistentLoopSites.gasSteps_join s frame
    (by simp [frame, PersistentFrame.frame]; omega) hrun hcode hfork hnp))

def gasSteps_empty (s : State) (off limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hempty : s.executionEnv.calldata.size = 0)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 335, stack := off :: limit :: rho}
      {s with pc := UInt256.ofNat 365, stack := PersistentFrame.frame StackRunBridge.initialHashState off limit rho} := by
  let frame := PersistentFrame.frame StackRunBridge.initialHashState off limit rho
  have gi := gasSteps_initial s off limit rho hstack hrun hcode hfork hnp
  have gt : GasSteps {s with pc := UInt256.ofNat 360, stack := frame}
      {s with pc := UInt256.ofNat 365, stack := frame} := by
    apply PadLift.gasSteps_of_raw testSite {s with pc := UInt256.ofNat 360, stack := frame} _
      hcode hfork hrun hnp test_pc.symm
    · apply PadLift.advancesAll_sound
      decide
    · have hraw := run_empty s (UInt256.ofNat 360) frame 504
        (by simp [frame, PersistentFrame.frame]; omega) hrun hempty
      have hp : pcAfter (UInt256.ofNat 360) (testTemplate 504) = UInt256.ofNat 365 := by decide
      rw [hp] at hraw
      exact hraw
  exact gi.trans gt

#print axioms gasSteps_positive
#print axioms gasSteps_empty
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStart
