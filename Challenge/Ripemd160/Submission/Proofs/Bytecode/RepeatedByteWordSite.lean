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
  [.push 1 97, .push 1 255, .push 0 0, .op .NOT, .op .DIV, .op .MUL]

private theorem template_slice :
    (A.instructions.drop 25).take template.length = template := by rfl

private theorem template_wellFormed : ∀ instruction ∈ template,
    DataStepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def site : GenericRoundSite A .Osaka template :=
  StackSiteBuilder.ofSlice _ 25 template_slice (by
    change 25 + template.length ≤ Artifact.submissionInstructions.length
    rw [Artifact.referenceInstructions_count]
    decide) StackRoundData.artifact_code_bound template_wellFormed (by decide)

theorem site_start : site.startPC = UInt256.ofNat 38 := by rfl
theorem site_end : site.endPC = UInt256.ofNat 46 := by rfl

private theorem run_word (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc template, stack := KnownInputData.fullWord :: rho} := by
  have h0 : rho.length < 1024 := by omega
  have h1 : rho.length + 1 < 1024 := by omega
  have h2 : rho.length + 2 < 1024 := by omega
  have h3 : rho.length + 3 < 1024 := by omega
  have hzero : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  have hproduct : PatternedSwar.M * UInt256.ofNat 97 =
      KnownInputData.fullWord := by decide
  simp [Nat.add_assoc, h3, template, runInstrSeq, DataStepper.runInstr, hrun, h0, h1, h2, hzero,
    pcAfter, Instr.size, UInt256.succ,
    Word.literal_eq_ofNat, CompactGuardConstants.repeated_one_ofNat, hadd, hproduct]

private theorem advances {instruction : Instr} {s t : State}
    (hmem : instruction ∈ template) (hresult : DataStepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  apply RepeatedByteWord.advances (UInt256.ofNat 97) ?_ hresult
  simp only [template, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [RepeatedByteWord.code, Word.literal_eq_ofNat]

private theorem run_located (s : State) (rho : List UInt256)
    (hstack : rho.length < 1021) (hrun : s.halt = .Running) :
    DataStepper.runLocatedBlock site.path {s with pc := site.startPC, stack := rho} =
      some {s with pc := site.endPC, stack := KnownInputData.fullWord :: rho} := by
  have hend : site.endPC = pcAfter site.startPC template := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  have hraw : DataStepper.runLocatedBlock site.path {s with pc := site.startPC, stack := rho} =
      runInstrSeq template {s with pc := site.startPC, stack := rho} := by
    apply runLocatedBlock_eq_runInstrSeq_site site _ rfl
    intro located hmem u v hresult
    apply advances ?_ hresult
    rw [← site.instruction_eq]
    exact List.mem_map_of_mem hmem
  rw [hraw, run_word s site.startPC rho hstack hrun, ← hend]

def gasSteps_fullWord (s : State) (rho : List UInt256) (hstack : rho.length < 1021)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 38, stack := rho}
      {s with pc := UInt256.ofNat 46, stack := KnownInputData.fullWord :: rho} := by
  have g : GasSteps {s with pc := site.startPC, stack := rho}
      {s with pc := site.endPC, stack := KnownInputData.fullWord :: rho} := by
    apply DataStepper.runLocatedBlock_sound A .Osaka site.path
    · exact hcode
    · exact hfork
    · exact run_located s rho hstack hrun
    · exact hrun
    · exact hnp
  exact g.cast (by rw [site_start]) (by rw [site_end])

#print axioms gasSteps_fullWord

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWordSite
