import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalRound
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineBoundarySites

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalRoundSite
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace PairedAllInlineCoreTrace TerminalRound CachedCoreCommon

def template : List Instr := modifiedTemplate ++ coreExitTemplate

theorem template_slice :
    (Artifact.submissionArtifact.instructions.drop 3854).take template.length = template := by
  rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3854 template_slice
    (by
      change 3855 + template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)

theorem site_startPC : site.startPC = UInt256.ofNat 4569 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3854) = UInt256.ofNat 4569
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem run_template (s : State) (q : PairedHelperBooleanTrace.Frame)
    (ret : UInt256) (rho : List UInt256) (hstack : (ret :: rho).length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := UInt256.ofNat 4569, stack := inline79Entry q (cache s.memory ++ (ret :: rho))} =
      some {s with pc := UInt256.ofNat 4616, stack := PairedAllInlineBoundarySites.cachedTailEntry s.memory (modifiedFrame s.memory q) ret rho} := by
  have hs : (cache s.memory ++ (ret :: rho)).length ≤ 1002 := by simp only [List.length_append, cache_length]; omega
  let post : PairedHelperBooleanTrace.Frame :=
    {q with a := q.e, b := modifiedT (inline79Frame s.memory q) (PairedHelperBooleanTrace.inline4Boolean q), c := q.b, d := modifiedC10 q, e := q.d}
  have h0 := run_modifiedTemplate_raw s (UInt256.ofNat 4569) q (cache s.memory ++ (ret :: rho)) hs hrun hactive
  rw [modifiedTemplate_pc] at h0
  have h1 := run_coreExitTemplate s (UInt256.ofNat 4614) post (cache s.memory ++ (ret :: rho)) hs hrun
  have hpc : pcAfter (UInt256.ofNat 4614) coreExitTemplate = UInt256.ofNat 4616 := by decide
  rw [hpc] at h1
  exact DenseScheduleTrace.runInstrSeq_append_running h0 hrun h1

def gasSteps_round (s : State) (q : PairedHelperBooleanTrace.Frame)
    (ret : UInt256) (rho : List UInt256) (hstack : (ret :: rho).length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4569, stack := inline79Entry q (cache s.memory ++ (ret :: rho))}
      {s with pc := UInt256.ofNat 4616, stack := PairedAllInlineBoundarySites.cachedTailEntry s.memory (modifiedFrame s.memory q) ret rho} := by
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp
    site_startPC.symm
    (by apply PairedHelperBooleanTrace.coreAdvancesAll_sound; decide)
    (run_template s q ret rho hstack hrun hactive)

def gasSteps_suffix (s : State) (q : PairedHelperBooleanTrace.Frame)
    (ret : UInt256) (rho : List UInt256) (hstack : (ret :: rho).length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4569, stack := inline79Entry q (cache s.memory ++ (ret :: rho))}
      {s with pc := ret, stack := rho, memory := PairedTailTrace.resultMemory s.memory (modifiedFrame s.memory q)} :=
  (gasSteps_round s q ret rho hstack hrun hactive hcode hfork hnp).trans
    (PairedAllInlineBoundarySites.gasSteps_tail s ret (modifiedFrame s.memory q) rho
      (by simp only [List.length_cons] at hstack; omega) hrun hactive hvalid hcode hfork hnp)

#print axioms gasSteps_suffix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalRoundSite
