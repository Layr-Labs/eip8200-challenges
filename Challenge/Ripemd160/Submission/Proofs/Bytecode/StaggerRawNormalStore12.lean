import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore12
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
def template : List Instr :=
  [ .op (.Dup ⟨7, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 120),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 110),
    .op .MSTORE,
    .op (.Dup ⟨6, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 100),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 90),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 70),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 60),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 50),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 40),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 30),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 20),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 10),
    .op .MSTORE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MSTORE ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0, x.v1, x.v2, x.v3, x.v4, x.v5, x.v6, x.v7 ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [  ] ++ rho
def outputMemory (memory : ByteArray) (x : Input) : ByteArray :=
  (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord memory 120 x.v7) 110 x.v0) 100 x.v7) 90 x.v1) 80 x.v2) 70 x.v3) 60 x.v3) 50 x.v4) 40 x.v5) 30 x.v5) 20 x.v6) 10 x.v7) 0 x.v7)
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho, memory := outputMemory s.memory x} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 12) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Table80Raw.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, outputStack, outputMemory, PairedScheduleMemory.writeWord,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_actual
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 568).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 568 actual_slice
    (by change 568 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 883 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 568) = UInt256.ofNat 883
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 883, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 926, stack := outputStack s.memory x rho, memory := outputMemory s.memory x} := by
  have hraw := run_actual s (UInt256.ofNat 883) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 883) template = UInt256.ofNat 926 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore12
