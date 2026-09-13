import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalPool
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
def template : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op .MLOAD,
    .op (.Dup ⟨1, by decide⟩),
    .op .AND,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 48),
    .op .MLOAD,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 20),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 44),
    .op .MLOAD,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 56),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 52),
    .op .MLOAD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 40),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 28),
    .op .MLOAD,
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨9, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 60),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 4),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .MLOAD,
    .op (.Dup ⟨13, by decide⟩),
    .op .AND,
    .op (.Dup ⟨13, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 36),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .MLOAD,
    .op (.Dup ⟨15, by decide⟩),
    .op .AND,
    .op (.Swap ⟨14, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 12),
    .op .MLOAD,
    .op .AND ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0 ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land (MachineState.readWord memory 12) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 36)),
    (UInt256.land x.v0 (MachineState.readWord memory 32)),
    (MachineState.readWord memory 4),
    (MachineState.readWord memory 8),
    (UInt256.land x.v0 (MachineState.readWord memory 60)),
    (UInt256.land x.v0 (MachineState.readWord memory 28)),
    (UInt256.land x.v0 (MachineState.readWord memory 40)),
    (UInt256.land x.v0 (MachineState.readWord memory 52)),
    (UInt256.land x.v0 (MachineState.readWord memory 56)),
    (UInt256.land x.v0 (MachineState.readWord memory 44)),
    (UInt256.land x.v0 (MachineState.readWord memory 20)),
    (UInt256.land x.v0 (MachineState.readWord memory 48)),
    (MachineState.readWord memory 0),
    (UInt256.land x.v0 (MachineState.readWord memory 16)),
    (UInt256.land x.v0 (MachineState.readWord memory 24)) ] ++ rho
def actualOutput (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land (MachineState.readWord memory 12) x.v0),
    (UInt256.land (MachineState.readWord memory 36) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 32)),
    (MachineState.readWord memory 4),
    (MachineState.readWord memory 8),
    (UInt256.land (MachineState.readWord memory 60) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 28)),
    (UInt256.land (MachineState.readWord memory 40) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 52)),
    (UInt256.land (MachineState.readWord memory 56) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 44)),
    (UInt256.land (MachineState.readWord memory 20) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 48)),
    (MachineState.readWord memory 0),
    (UInt256.land x.v0 (MachineState.readWord memory 16)),
    (UInt256.land x.v0 (MachineState.readWord memory 24)) ] ++ rho
private theorem actualOutput_eq (memory : ByteArray) (x : Input) (rho : List UInt256) :
    actualOutput memory x rho = outputStack memory x rho := by
  simp only [actualOutput, outputStack, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
private theorem run_generated (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := actualOutput s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 22) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, actualOutput,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  simpa only [actualOutput_eq] using run_generated s pc x rho hstack hrun hactive
#print axioms run_actual
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 334).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 334 actual_slice
    (by change 334 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 569 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 334) = UInt256.ofNat 569
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 569, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 642, stack := outputStack s.memory x rho} := by
  have hraw := run_actual s (UInt256.ofNat 569) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 569) template = UInt256.ofNat 642 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalPool
