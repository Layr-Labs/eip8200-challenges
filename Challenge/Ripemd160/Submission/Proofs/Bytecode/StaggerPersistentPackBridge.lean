import Challenge.Ripemd160.Submission.Proofs.Bytecode.JointRightPackModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCoreRight
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCore
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPackBridge
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
open JointRightPackRaw (template)

abbrev suffix := JointRightPackModel.suffix
abbrev input := JointRightPackModel.input
abbrev input_eq := JointRightPackModel.input_eq
abbrev output_eq := JointRightPackModel.output_eq

def entry (s : State) (h q : WordLane) (off limit : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 937, stack := stack s.memory h.e [.d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500] q h (UInt256.ofNat 1352829926) (suffix h off limit rho)}

theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 537).take template.length = template := by rfl

def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 537 actual_slice
    (by change 537 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 937 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 537) = UInt256.ofNat 937
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (h q : WordLane) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s h q off limit rho)
      (StaggerCore.atRound s h.e 0 (StaggerCoreModel.pair h (StaggerCoreModel.right2 s.memory q)) h (suffix h off limit rho)) := by
  have raw := JointRightPackRaw.run_actual s (UInt256.ofNat 937)
    (input s.memory h q off limit) rho hs hr ha (by rfl)
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 937) template = UInt256.ofNat 1041 := by decide
  rw [hend] at raw
  have g := DenseScheduleLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 937, stack := JointRightPackRaw.inputStack (input s.memory h q off limit) rho}
    {s with pc := UInt256.ofNat 1041, stack := JointRightPackRaw.outputStack s.memory (input s.memory h q off limit) rho}
    hcode hfork hr hnp site_pc.symm advances raw
  rw [input_eq, output_eq] at g
  exact g

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentPackBridge
