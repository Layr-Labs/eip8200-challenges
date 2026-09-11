import Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Round
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreCommon

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Site
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace PairedAllInlineCoreTrace Strip78Round CachedCoreCommon

theorem template_slice :
    (Artifact.submissionArtifact.instructions.drop 3809).take stripTemplate.length = stripTemplate := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka stripTemplate :=
  StackSiteBuilder.ofSlice stripTemplate 3809 template_slice
    (by
      change 3809 + stripTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := stripTemplate) (by decide))
    (by decide)

theorem site_startPC : site.startPC = UInt256.ofNat 4532 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3809) = UInt256.ofNat 4532
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem stripTemplate_pc : pcAfter (UInt256.ofNat 4532) stripTemplate = UInt256.ofNat 4578 := by decide

def gasSteps (s : State) (f : PairedHelperBooleanTrace.CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4532, stack := inline78Entry f.frame rho}
      {s with pc := UInt256.ofNat 4578, stack := inline79Entry (dirtyFrame s.memory f) rho} := by
  have hraw := run_stripTemplate s (UInt256.ofNat 4532) f.frame rho hstack hrun hactive
  rw [stripTemplate_pc, output_dirtyFrame] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp
    site_startPC.symm
    (by apply PairedHelperBooleanTrace.coreAdvancesAll_sound; decide)
    hraw

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Site
