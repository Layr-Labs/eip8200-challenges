import Challenge.Ripemd160.Submission.Local20261028.PadValues
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
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
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadRawLeft79
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
def template : List Instr :=
  [ .op (.Swap ⟨11, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨14, by decide⟩),
    .op .NOT,
    .op .OR,
    .op .XOR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op .ADD,
    .op (.Dup ⟨15, by decide⟩),
    .op .AND,
    .op (.Dup ⟨14, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 27),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .ADD ]
def inputStack (n : UInt256) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0,
    x.v1,
    x.v2,
    x.v3,
    x.v4,
    x.v5,
    (PadValues.load n 360),
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    (UInt256.ofNat 23),
    (UInt256.ofNat 2840853838),
    x.v13,
    x.v14,
    x.v15,
    x.v16,
    x.v17,
    x.v18,
    x.v19 ] ++ rho
def outputStack (n : UInt256) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.add (UInt256.shiftRight (UInt256.mul x.v14 (UInt256.land x.v15 (UInt256.add (UInt256.add (PadValues.load n 198) (UInt256.add x.v4 (UInt256.xor (UInt256.lor (UInt256.lnot x.v0) x.v2) x.v1))) (UInt256.ofNat 2840853838)))) (UInt256.ofNat 27)) x.v3),
    x.v1,
    x.v2,
    x.v3,
    x.v4,
    x.v5,
    (PadValues.load n 360),
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    (UInt256.ofNat 23),
    x.v0,
    x.v13,
    x.v14,
    x.v15,
    x.v16,
    x.v17,
    x.v18,
    x.v19 ] ++ rho
def actualOutput (n : UInt256) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.add (UInt256.shiftRight (UInt256.mul x.v14 (UInt256.land x.v15 (UInt256.add (UInt256.add (PadValues.load n 198) (UInt256.add x.v4 (UInt256.xor (UInt256.lor (UInt256.lnot x.v0) x.v2) x.v1))) (UInt256.ofNat 2840853838)))) (UInt256.ofNat 27)) x.v3),
    x.v1,
    x.v2,
    x.v3,
    x.v4,
    x.v5,
    (PadValues.load n 360),
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    (UInt256.ofNat 23),
    x.v0,
    x.v13,
    x.v14,
    x.v15,
    x.v16,
    x.v17,
    x.v18,
    x.v19 ] ++ rho
private theorem actualOutput_eq (n : UInt256) (x : Input) (rho : List UInt256) :
    actualOutput n x rho = outputStack n x rho := by rfl
private theorem run_generated (s : State) (pc n : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 901) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack n x rho} =
      some {s with pc := pcAfter pc template, stack := actualOutput n x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 48) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, actualOutput, PadValues.load,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [PadValues.add_zero, PadValues.zero_add, PadValues.xor_zero, PadValues.zero_xor, neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem run_actual (s : State) (pc n : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 901) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack n x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack n x rho} := by
  simpa only [actualOutput_eq] using run_generated s pc n x rho hstack hrun hactive
#print axioms run_actual
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadRawLeft79
