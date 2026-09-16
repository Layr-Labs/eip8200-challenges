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
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired15
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
def template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨7, by decide⟩),
    .op (.Dup ⟨13, by decide⟩),
    .op .AND,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op .OR,
    .op .XOR,
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 1018),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .push ⟨13, by decide⟩ (UInt256.ofNat 20123953283308614743486684463105),
    .op (.Dup ⟨13, by decide⟩),
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op .MULMOD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .SHR,
    .op (.Dup ⟨8, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op (.Swap ⟨5, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .MUL,
    .op (.Dup ⟨7, by decide⟩),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0,
    x.v7,
    x.v2,
    x.v3,
    x.v4,
    x.v5,
    x.v6,
    (UInt256.ofNat 23),
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16 ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land x.v3 (UInt256.shiftRight (UInt256.mul x.v10 x.v6) (UInt256.ofNat 23))),
    x.v0,
    x.v2,
    x.v3,
    x.v4,
    x.v5,
    (UInt256.land x.v3 (UInt256.add x.v8 (UInt256.shiftRight (UInt256.mulMod (UInt256.land x.v3 (UInt256.add x.v5 (UInt256.add (MachineState.readWord memory 990) (UInt256.add (UInt256.xor x.v9 (UInt256.xor (UInt256.lor (UInt256.land x.v0 x.v4) (UInt256.xor (UInt256.land x.v9 x.v4) x.v6)) x.v0)) x.v7)))) (UInt256.ofNat 20123953283308614743486684463105) x.v12) (UInt256.ofNat 24)))),
    (UInt256.ofNat 23),
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16 ] ++ rho
def actualOutput (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land x.v3 (UInt256.shiftRight (UInt256.mul x.v10 x.v6) (UInt256.ofNat 23))),
    x.v0,
    x.v2,
    x.v3,
    x.v4,
    x.v5,
    (UInt256.land x.v3 (UInt256.add x.v8 (UInt256.shiftRight (UInt256.mulMod (UInt256.land x.v3 (UInt256.add x.v5 (UInt256.add (MachineState.readWord memory 990) (UInt256.add (UInt256.xor x.v9 (UInt256.xor (UInt256.lor (UInt256.land x.v0 x.v4) (UInt256.xor (UInt256.land x.v9 x.v4) x.v6)) x.v0)) x.v7)))) (UInt256.ofNat 20123953283308614743486684463105) x.v12) (UInt256.ofNat 24)))),
    (UInt256.ofNat 23),
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16 ] ++ rho
private theorem actualOutput_eq (memory : ByteArray) (x : Input) (rho : List UInt256) :
    actualOutput memory x rho = outputStack memory x rho := by rfl
private theorem run_generated (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := actualOutput s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 23) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, actualOutput,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  simpa only [actualOutput_eq] using run_generated s pc x rho hstack hrun hactive
#print axioms run_actual

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired15
