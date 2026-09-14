import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawLeft77
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
def template : List Instr :=
  [ .op (.Dup ⟨9, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .op (.Dup ⟨7, by decide⟩),
    .op .SHR,
    .op (.Dup ⟨8, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op (.Dup ⟨13, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op (.Dup ⟨13, by decide⟩),
    .op .NOT,
    .op .OR,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MLOAD,
    .op (.Dup ⟨7, by decide⟩),
    .op .ADD,
    .op .ADD,
    .op .ADD,
    .op .AND,
    .op (.Dup ⟨13, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 25),
    .op .SHR,
    .op .ADD,
    .op (.Dup ⟨13, by decide⟩),
    .op .AND,
    .op (.Dup ⟨1, by decide⟩) ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v10,
    x.v5,
    x.v0,
    x.v7,
    x.v8,
    x.v9,
    (UInt256.ofNat 23),
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16,
    x.v17,
    x.v18,
    x.v19 ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v2,
    (UInt256.land x.v14 (UInt256.add x.v3 (UInt256.shiftRight (UInt256.mul x.v13 (UInt256.land x.v14 (UInt256.add x.v0 (UInt256.add (MachineState.readWord memory 0) (UInt256.add (UInt256.xor x.v7 (UInt256.lor x.v1 (UInt256.lnot x.v2))) x.v6))))) (UInt256.ofNat 25)))),
    x.v2,
    (UInt256.shiftRight (UInt256.mul x.v13 x.v1) (UInt256.ofNat 23)),
    x.v10,
    x.v5,
    x.v0,
    x.v7,
    x.v8,
    x.v9,
    (UInt256.ofNat 23),
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16,
    x.v17,
    x.v18,
    x.v19 ] ++ rho
def actualOutput (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v2,
    (UInt256.land x.v14 (UInt256.add x.v3 (UInt256.shiftRight (UInt256.mul x.v13 (UInt256.land x.v14 (UInt256.add x.v0 (UInt256.add (MachineState.readWord memory 0) (UInt256.add (UInt256.xor x.v7 (UInt256.lor x.v1 (UInt256.lnot x.v2))) x.v6))))) (UInt256.ofNat 25)))),
    x.v2,
    (UInt256.shiftRight (UInt256.mul x.v13 x.v1) (UInt256.ofNat 23)),
    x.v10,
    x.v5,
    x.v0,
    x.v7,
    x.v8,
    x.v9,
    (UInt256.ofNat 23),
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16,
    x.v17,
    x.v18,
    x.v19 ] ++ rho
private theorem actualOutput_eq (memory : ByteArray) (x : Input) (rho : List UInt256) :
    actualOutput memory x rho = outputStack memory x rho := by rfl
private theorem run_generated (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (haliasA : x.v9 = x.v1) (haliasE : x.v10 = x.v6) (haliasD : x.v11 = x.v2) (haliasR : x.v8 = x.v3) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := actualOutput s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 48) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, actualOutput,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap, haliasA, haliasE, haliasD, haliasR,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (haliasA : x.v9 = x.v1) (haliasE : x.v10 = x.v6) (haliasD : x.v11 = x.v2) (haliasR : x.v8 = x.v3) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  simpa only [actualOutput_eq] using run_generated s pc x rho hstack haliasA haliasE haliasD haliasR hrun hactive
#print axioms run_actual
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 3443).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3443 actual_slice
    (by change 3443 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4490 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3443) = UInt256.ofNat 4490
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (haliasA : x.v9 = x.v1) (haliasE : x.v10 = x.v6) (haliasD : x.v11 = x.v2) (haliasR : x.v8 = x.v3) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4490, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 4521, stack := outputStack s.memory x rho} := by
  have hraw := run_actual s (UInt256.ofNat 4490) x rho hstack haliasA haliasE haliasD haliasR hrun hactive
  have hend : pcAfter (UInt256.ofNat 4490) template = UInt256.ofNat 4521 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawLeft77
