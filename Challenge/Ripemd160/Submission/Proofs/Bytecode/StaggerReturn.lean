import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerReturn
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

def template : List Instr := [.op .JUMP]
theorem slice : (Artifact.submissionArtifact.instructions.drop 3869).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3869 slice
    (by change 3869 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem pc : site.startPC = UInt256.ofNat 4689 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3869) = UInt256.ofNat 4689
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps (s : State) (ret : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4689, stack := ret :: rho}
      {s with pc := ret, stack := rho} := by
  apply PadLift.gasSteps_of_raw site {s with pc := UInt256.ofNat 4689, stack := ret :: rho}
    _ hcode hfork hr hnp pc.symm (by simp [template])
  have hc : rho.length + 1 < 1024 := by omega
  simp [template, runInstrSeq, Stepper.runInstr, hr, hv, hc]
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerReturn
