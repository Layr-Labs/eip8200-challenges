import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace

abbrev A := Artifact.submissionArtifact

def template : List Instr :=
  [.push 32 KnownInputData.fullWord,
   .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST]

private theorem template_slice :
    (A.instructions.drop 116).take template.length = template := by rfl

private theorem template_wellFormed : ∀ instruction ∈ template,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

private theorem template_advances : ∀ instruction ∈ template,
    SharedCallTrace.Advances instruction := by
  intro instruction hmem
  simp only [template, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def site : GenericRoundSite A .Osaka template :=
  StackSiteBuilder.ofSlice _ 116 template_slice (by
    change 116 + template.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) StackRoundData.artifact_code_bound template_wellFormed (by decide)

theorem site_start : site.startPC = UInt256.ofNat 194 := by rfl
theorem site_end : site.endPC = UInt256.ofNat 232 := by rfl

private theorem run_template (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc template, stack := KnownInputData.fullWord :: rho} := by
  have h0 : rho.length < 1024 := by omega
  have h1 : rho.length + 1 < 1024 := by omega
  simp [template, runInstrSeq, Stepper.runInstr, pcAfter, hrun, h0, h1,
    UInt256.succ, Instr.size, Instr.size_push, Instr.size_op]

private theorem run_located {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork template)
    (s : State) (rho : List UInt256) (hstack : rho.length < 1021)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := rho} =
      some {s with pc := site.endPC, stack := KnownInputData.fullWord :: rho} := by
  have hend : site.endPC = pcAfter site.startPC template := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [SharedCallTrace.runLocatedBlock_eq_raw site template_advances _ rfl]
  rw [run_template s site.startPC rho hstack hrun, ← hend]

def gasSteps_fullWord (s : State) (rho : List UInt256) (hstack : rho.length < 1021)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 194, stack := rho}
      {s with pc := UInt256.ofNat 232, stack := KnownInputData.fullWord :: rho} := by
  have g := Stepper.runLocatedBlock_sound A .Osaka site.path
    hcode hfork (run_located site s rho hstack hrun) hrun hnp
  exact g.cast (by rw [site_start]) (by rw [site_end])

#print axioms gasSteps_fullWord
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
