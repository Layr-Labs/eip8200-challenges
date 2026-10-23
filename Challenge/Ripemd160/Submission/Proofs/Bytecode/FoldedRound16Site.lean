import Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedCandidateArtifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedRound16
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerCorePaired16
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedRound16Site
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw StaggerCoreCommon
open Paired144WordRound Paired144WordRotation
open FoldedCandidateArtifact (artifact)
abbrev template := FoldedRound16.template

theorem actual_slice : (artifact.instructions.drop 1064).take template.length = template := by rfl
private theorem code_bound : artifact.code.size < 2^256 := by
  change FoldedCandidateArtifact.code.size < 2^256
  rw [FoldedCandidateArtifact.code_size]
  decide

def site : StackRoundTemplate.GenericRoundSite artifact .Osaka template :=
  StackSiteBuilder.ofSlice template 1064 actual_slice
    (by change 1064 + template.length ≤ FoldedCandidateArtifact.instructions.length
        rw [FoldedCandidateArtifact.instruction_count]; decide)
    code_bound (HoistedInherited.StackRoundData.templateWellFormed_mem (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 1730 := by
  change UInt256.ofNat (artifact.instructionPC 1064) = UInt256.ofNat 1730
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply HoistedInherited.Table80SiteCommon.coreAdvancesAll_sound
  decide

/-- Located, gas-aware correctness of the actual changed round, for arbitrary
memory, state, stack tail and RIPEMD working words. The resident key must be the
round-15 key; replacing an arbitrary key by this literal is NOT justified. -/
def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hkey : x.v5 = UInt256.ofNat 34535016170389834383797866734609369064725060249452544)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 1730, stack := StaggerRawPaired16.inputStack x rho}
      {s with pc := UInt256.ofNat 1794, stack := StaggerRawPaired16.outputStack s.memory x rho} := by
  have hraw := FoldedRound16.run_original s (UInt256.ofNat 1730) x rho hstack hrun hactive hkey
  have hend : pcAfter (UInt256.ofNat 1730) template = UInt256.ofNat 1794 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw

/-- RIPEMD semantic bridge: the exact candidate's relocated round implements
round 16 for every working state and memory, not only the public scoring vectors. -/
def semantic (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 1730, stack := stack s.memory h4 [.d, .cache 140, .e, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500] q right (StaggerAlgorithm.physicalKey 15) rho} {s with pc := UInt256.ofNat 1794, stack := stack s.memory h4 [.d, .cache 140, .a, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500] (HoistedInherited.StaggerCorePaired16.eval s.memory q) right (StaggerAlgorithm.physicalKey 16) rho} := by
  have hk : (HoistedInherited.StaggerCorePaired16.input s.memory h4 q right
      (StaggerAlgorithm.physicalKey 15)).v5 =
      UInt256.ofNat 34535016170389834383797866734609369064725060249452544 := by
    change StaggerAlgorithm.physicalKey 15 = _
    decide
  have g := gasSteps s (HoistedInherited.StaggerCorePaired16.input s.memory h4 q right
    (StaggerAlgorithm.physicalKey 15)) rho hstack hrun hactive hk hcode hfork hnp
  rw [HoistedInherited.StaggerCorePaired16.output_eq] at g
  exact g
#print axioms actual_slice
#print axioms gasSteps
#print axioms semantic
end Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedRound16Site
