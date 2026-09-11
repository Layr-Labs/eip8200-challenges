import Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalRoundSite

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateSite
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace PairedAllInlineCoreTrace PenultimateFinish CachedCoreCommon

theorem template_slice :
    (Artifact.submissionArtifact.instructions.drop 3811).take PenultimateTemplate.code.length =
      PenultimateTemplate.code := by
  rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka PenultimateTemplate.code :=
  StackSiteBuilder.ofSlice PenultimateTemplate.code 3811 template_slice
    (by
      change 3811 + PenultimateTemplate.code.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := PenultimateTemplate.code) (by decide))
    (by decide)

theorem site_startPC : site.startPC = UInt256.ofNat 4519 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3811) = UInt256.ofNat 4519
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def gasSteps_round (s : State) (q : PairedHelperBooleanTrace.Frame)
    (ret : UInt256) (rho : List UInt256) (hstack : (ret :: rho).length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4519, stack := inline78Entry q (cache s.memory ++ (ret :: rho))}
      {s with
        pc := UInt256.ofNat 4565
        stack := inline79Entry (dirty78Frame s.memory q) (cache s.memory ++ (ret :: rho))} := by
  have hs : (cache s.memory ++ (ret :: rho)).length ≤ 1002 := by
    simp only [List.length_append, cache_length]
    omega
  have h := PenultimateTemplate.run_code s (UInt256.ofNat 4519) q
    (cache s.memory ++ (ret :: rho)) hs hrun hactive
  rw [PenultimateTemplate.pc_code] at h
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp
    site_startPC.symm
    (by apply PairedHelperBooleanTrace.coreAdvancesAll_sound; decide) h

def gasSteps_suffix (s : State) (q : PairedHelperBooleanTrace.Frame)
    (ret : UInt256) (rho : List UInt256) (hstack : (ret :: rho).length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4519, stack := inline78Entry q (cache s.memory ++ (ret :: rho))}
      {s with
        pc := ret
        stack := rho
        memory := PairedTailTrace.resultMemory s.memory
          (TerminalRound.modifiedFrame s.memory (dirty78Frame s.memory q))} :=
  (gasSteps_round s q ret rho hstack hrun hactive hcode hfork hnp).trans
    (TerminalRoundSite.gasSteps_suffix s (dirty78Frame s.memory q) ret rho hstack
      hrun hactive hvalid hcode hfork hnp)

#print axioms gasSteps_suffix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateSite
