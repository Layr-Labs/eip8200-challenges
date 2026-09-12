import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore44
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
def template : List Instr :=
  [ .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 440),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 430),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 420),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 410),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 400),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 390),
    .op .MSTORE,
    .op (.Dup ⟨11, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 380),
    .op .MSTORE,
    .op (.Dup ⟨10, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 370),
    .op .MSTORE,
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 360),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 350),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 340),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 330),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 320),
    .op .MSTORE,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 310),
    .op .MSTORE,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 300),
    .op .MSTORE,
    .op (.Dup ⟨9, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 290),
    .op .MSTORE ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0, x.v1, x.v2, x.v3, x.v4, x.v5, x.v6, x.v7, x.v8, x.v9, x.v10, x.v11, x.v12, x.v13, x.v14 ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v1,
    x.v2,
    x.v3,
    x.v4,
    x.v5,
    x.v6,
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12,
    x.v13,
    x.v14 ] ++ rho
def outputMemory (memory : ByteArray) (x : Input) : ByteArray :=
  (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord memory 440 x.v0) 430 x.v1) 420 x.v2) 410 x.v2) 400 x.v0) 390 x.v2) 380 x.v12) 370 x.v11) 360 x.v6) 350 x.v4) 340 x.v4) 330 x.v9) 320 x.v9) 310 x.v8) 300 x.v8) 290 x.v10)
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho, memory := outputMemory s.memory x} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 19) : rho.length + n < 1024 := by omega
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
    (Artifact.submissionArtifact.instructions.drop 479).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 479 actual_slice
    (by change 479 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 743 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 479) = UInt256.ofNat 743
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
    GasSteps {s with pc := UInt256.ofNat 743, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 822, stack := outputStack s.memory x rho, memory := outputMemory s.memory x} := by
  have hraw := run_actual s (UInt256.ofNat 743) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 743) template = UInt256.ofNat 822 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore44
