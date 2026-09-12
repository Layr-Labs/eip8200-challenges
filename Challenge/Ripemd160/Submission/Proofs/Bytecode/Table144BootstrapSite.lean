import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Bootstrap
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144BootstrapSite
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Table144Bootstrap

theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 661).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 661 actual_slice
    (by change 661 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    Artifact.code_size_lt
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 1043 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 661) = UInt256.ofNat 1043
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

private def advancesCheck : Instr → Bool
  | .op .DIV | .op .SUB => true
  | instruction => PadLift.advancesCheck instruction

private theorem advancesCheck_sound (instruction : Instr) (h : advancesCheck instruction = true)
    {s t : State} (hresult : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  cases instruction with
  | push width value =>
    exact PadLift.runInstr_pc_extra (PadLift.advancesCheck_sound _ h) hresult
  | op operation =>
    cases operation <;> first
      | exact PairedDivMaskCache.runInstr_pc_div hresult
      | exact SharedCallTrace.runInstr_pc_of_advances (Or.inr (Or.inl rfl)) hresult
      | exact PadLift.runInstr_pc_extra (PadLift.advancesCheck_sound _ h) hresult
      | (rename_i inner; cases inner <;> first
          | exact PairedDivMaskCache.runInstr_pc_div hresult
          | exact SharedCallTrace.runInstr_pc_of_advances (Or.inr (Or.inl rfl)) hresult
          | exact PadLift.runInstr_pc_extra (PadLift.advancesCheck_sound _ h) hresult)

theorem advances : ∀ instruction ∈ template, ∀ {s t : State},
    Stepper.runInstr instruction s = some t → t.pc = s.pc + UInt256.ofNat instruction.size := by
  have hall : template.all advancesCheck = true := by decide
  intro instruction hi s t hr
  exact advancesCheck_sound instruction ((List.all_eq_true.mp hall) instruction hi) hr

def gasSteps (s : State) (h0 h1 h2 h3 h4 : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 991) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 1043, stack := [h0,h1,h2,h3,h4] ++ rho}
      {s with pc := UInt256.ofNat 1129, stack := resultStack h0 h1 h2 h3 h4 rho} := by
  apply Stepper.runLocatedBlock_sound _ _ site.path
  · exact hcode
  · exact hfork
  · have hpc : ({s with pc := UInt256.ofNat 1043, stack := [h0,h1,h2,h3,h4] ++ rho} : State).pc = site.startPC := site_pc.symm
    rw [runLocatedBlock_eq_runInstrSeq_site site _ hpc (by
      intro located hm u v hu
      apply advances _ ?_ hu
      rw [← site.instruction_eq]
      exact List.mem_map_of_mem hm)]
    have hraw := run_actual s (UInt256.ofNat 1043) h0 h1 h2 h3 h4 rho hstack hrun
    have hend : pcAfter (UInt256.ofNat 1043) template = UInt256.ofNat 1129 := by decide
    rw [hend] at hraw
    exact hraw
  · exact hrun
  · exact hnp
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144BootstrapSite
