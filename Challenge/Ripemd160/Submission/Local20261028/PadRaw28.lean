import Challenge.Ripemd160.Submission.Local20261028.CandidateBytes
import Challenge.Ripemd160.Submission.Local20261028.PadValues
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
set_option warningAsError true
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadRaw28
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
def template : List Instr :=
  [ .op (.Swap ⟨6, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op (.Dup ⟨12, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨12, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨22, by decide⟩ (UInt256.ofNat 40945789247971450477386360121479348807026276516919705),
    .op (.Swap ⟨10, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op (.Dup ⟨12, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op (.Swap ⟨10, by decide⟩),
    .op (.Dup ⟨12, by decide⟩),
    .op .MUL,
    .op (.Dup ⟨9, by decide⟩),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND ]
def inputStack (n : UInt256) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0,
    x.v15,
    x.v12,
    x.v7,
    (PadValues.load n 360),
    x.v3,
    x.v4,
    x.v5,
    x.v6,
    (UInt256.ofNat 23),
    (UInt256.ofNat 34535016170389834383797866734609369064725061767952793),
    x.v9,
    x.v10,
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16 ] ++ rho
def outputStack (n : UInt256) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land x.v3 (UInt256.shiftRight (UInt256.mul x.v10 x.v9) (UInt256.ofNat 23))),
    x.v15,
    x.v12,
    x.v7,
    (PadValues.load n 360),
    x.v3,
    x.v4,
    x.v0,
    x.v6,
    (UInt256.ofNat 23),
    (UInt256.ofNat 40945789247971450477386360121479348807026276516919705),
    (UInt256.land x.v3 (UInt256.add x.v7 (UInt256.shiftRight (UInt256.mul x.v10 (UInt256.land x.v3 (UInt256.add (UInt256.ofNat 34535016170389834383797866734609369064725061767952793) (UInt256.add (PadValues.load n 360) (UInt256.add (UInt256.lor (UInt256.land x.v6 x.v9) (UInt256.xor (UInt256.land (UInt256.xor x.v4 x.v6) (UInt256.lor x.v0 x.v9)) x.v0)) x.v5))))) (UInt256.ofNat 22)))),
    x.v10,
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16 ] ++ rho
def actualOutput (n : UInt256) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land x.v3 (UInt256.shiftRight (UInt256.mul x.v10 x.v9) (UInt256.ofNat 23))),
    x.v15,
    x.v12,
    x.v7,
    (PadValues.load n 360),
    x.v3,
    x.v4,
    x.v0,
    x.v6,
    (UInt256.ofNat 23),
    (UInt256.ofNat 40945789247971450477386360121479348807026276516919705),
    (UInt256.land x.v3 (UInt256.add x.v7 (UInt256.shiftRight (UInt256.mul x.v10 (UInt256.land x.v3 (UInt256.add (UInt256.ofNat 34535016170389834383797866734609369064725061767952793) (UInt256.add (PadValues.load n 360) (UInt256.add (UInt256.lor (UInt256.land x.v6 x.v9) (UInt256.xor (UInt256.land (UInt256.xor x.v4 x.v6) (UInt256.lor x.v0 x.v9)) x.v0)) x.v5))))) (UInt256.ofNat 22)))),
    x.v10,
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16 ] ++ rho
private theorem actualOutput_eq (n : UInt256) (x : Input) (rho : List UInt256) :
    actualOutput n x rho = outputStack n x rho := by rfl
private theorem run_generated (s : State) (pc n : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load n 162) :
    runInstrSeq template {s with pc := pc, stack := inputStack n x rho} =
      some {s with pc := pcAfter pc template, stack := actualOutput n x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, actualOutput, hcal, hmem, PadValues.load,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [PadValues.add_zero, PadValues.zero_add, PadValues.xor_zero, PadValues.zero_xor, neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals try simp only [PadValues.fold_one, PadValues.fold_two]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem run_actual (s : State) (pc n : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load n 162) :
    runInstrSeq template {s with pc := pc, stack := inputStack n x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack n x rho} := by
  simpa only [actualOutput_eq] using run_generated s pc n x rho hstack hrun hactive hcal hmem
#print axioms run_actual
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 5969).take 58 =
      PcEncoding.assembleBytes template := by
  rw [RipemdSubmissionTables20261028.CandidateBytes.exact_list]
  change (RipemdSubmissionTables20261028.CandidateBytes.bytes.drop (5952+17)).take 58 = _
  rw [← List.drop_drop, RipemdSubmissionTables20261028.CandidateBytes.drop93]
  decide +kernel
#print axioms exact_bytes

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadRaw28
