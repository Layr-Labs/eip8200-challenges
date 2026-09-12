import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentLoopRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144CallPrepare
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentLoopSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PersistentLoopRaw

def postTemplate : List Instr := PersistentLoopRaw.template 4704

theorem post_slice :
    (Artifact.submissionArtifact.instructions.drop 296).take postTemplate.length = postTemplate := by rfl

def postSite : GenericRoundSite Artifact.submissionArtifact .Osaka postTemplate :=
  StackSiteBuilder.ofSlice postTemplate 296 post_slice
    (by change 296 + postTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    Artifact.code_size_lt
    (StackRoundData.templateWellFormed_mem (instructions := postTemplate) (by decide))
    (by decide)

theorem post_pc : postSite.startPC = UInt256.ofNat 490 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 296) = UInt256.ofNat 490
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def joinTemplate : List Instr := [.op .JUMPDEST]

theorem join_slice :
    (Artifact.submissionArtifact.instructions.drop 307).take joinTemplate.length = joinTemplate := by rfl

def joinSite : GenericRoundSite Artifact.submissionArtifact .Osaka joinTemplate :=
  StackSiteBuilder.ofSlice joinTemplate 307 join_slice
    (by change 307 + joinTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    Artifact.code_size_lt
    (StackRoundData.templateWellFormed_mem (instructions := joinTemplate) (by decide))
    (by decide)

theorem join_pc : joinSite.startPC = UInt256.ofNat 504 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 307) = UInt256.ofNat 504
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_exit (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 4704).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3973 = 4704 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3973 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 4704 = true
  rw [hcode]
  exact h

def gasSteps_join (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 504, stack := rho}
      {s with pc := UInt256.ofNat 505, stack := rho} := by
  apply PadLift.gasSteps_of_raw joinSite {s with pc := UInt256.ofNat 504, stack := rho} _
    hcode hfork hrun hnp join_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · simp [joinTemplate, runInstrSeq, Stepper.runInstr, hrun, hstack]
    rfl

def gasSteps_continue (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hmiss : (nextOffset off).toNat ≠ limit.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 490, stack := PersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 505, stack := PersistentFrame.frame h (nextOffset off) limit rho} := by
  have gp : GasSteps {s with pc := UInt256.ofNat 490, stack := PersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 504, stack := PersistentFrame.frame h (nextOffset off) limit rho} := by
    apply PadLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 490, stack := PersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
    · apply PadLift.advancesAll_sound
      decide
    · have hraw := run_continue s (UInt256.ofNat 490) h off limit rho 4704 hstack hrun hmiss
      have hend : pcAfter (UInt256.ofNat 490) (PersistentLoopRaw.template 4704) = UInt256.ofNat 504 := by decide
      rw [hend] at hraw
      exact hraw
  exact gp.trans (gasSteps_join s (PersistentFrame.frame h (nextOffset off) limit rho)
    (by simp [PersistentFrame.frame]; omega) hrun hcode hfork hnp)

def gasSteps_exit (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hhit : (nextOffset off).toNat = limit.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 490, stack := PersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4704, stack := PersistentFrame.frame h (nextOffset off) limit rho} := by
  apply PadLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 490, stack := PersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · exact run_exit s (UInt256.ofNat 490) h off limit rho 4704 hstack hrun hhit (valid_exit s hcode)

#print axioms gasSteps_continue
#print axioms gasSteps_exit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentLoopSites
