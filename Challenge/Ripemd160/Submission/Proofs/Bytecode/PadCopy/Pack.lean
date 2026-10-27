import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerPersistentPackBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawPack
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullPrefix
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Pack
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
open HoistedInherited.StaggerPersistentPackBridge (suffix input input_eq output_eq)

abbrev template := PadCopy.RawPack.template

/-- The pad-only copy of the right-line pack, at its relocated address. -/
def entry (s : State) (h q : WordLane) (off limit : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4674, stack := stack s.memory h.e [.d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500] q h (UInt256.ofNat 1352829926) (suffix h off limit rho)}

theorem actual_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 3439).take template.length = template := by rfl

def site : StackRoundTemplate.GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3439 actual_slice
    (by change 3439 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4674 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 3439) = UInt256.ofNat 4674
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply HoistedInherited.Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (h q : WordLane) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) :
    GasSteps (entry s h q off limit rho)
      (PadCopy.FullPrefix.atRound s h.e 0 (StaggerCoreModel.pair h (StaggerCoreModel.right2 s.memory q)) h (suffix h off limit rho)) := by
  have raw := PadCopy.RawPack.run_actual s (UInt256.ofNat 4674)
    (input s.memory h q off limit) rho hs hr ha (by rfl) (hz 14 (by decide))
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 4674) template = UInt256.ofNat 4774 := by decide
  rw [hend] at raw
  have g := DenseScheduleLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 4674, stack := JointRightPackRaw.inputStack (input s.memory h q off limit) rho}
    {s with pc := UInt256.ofNat 4774, stack := JointRightPackRaw.outputStack s.memory (input s.memory h q off limit) rho}
    hcode hfork hr hnp site_pc.symm advances raw
  rw [input_eq, output_eq] at g
  exact g

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Pack
