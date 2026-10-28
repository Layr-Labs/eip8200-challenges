import Challenge.Ripemd160.Submission.Local20261028.CandidateBytes
import Challenge.Ripemd160.Submission.Local20261028.PadValues
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
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
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadRawRight1
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
def template : List Instr :=
  [ .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 4601),
    .op .JUMP,
    .op .JUMPDEST,
    .op (.Dup ⟨15, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .NOT,
    .op .OR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MLOAD,
    .op (.Dup ⟨14, by decide⟩),
    .op .ADD,
    .op .ADD,
    .push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
    .op .ADD,
    .op .AND,
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .ADD,
    .op .AND,
    .push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
    .op (.Dup ⟨14, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 23),
    .op .SHR ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [     x.v3,
    x.v4,
    x.v0,
    x.v6,
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12 ] ++ rho
def outputStack (n : UInt256) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.shiftRight (UInt256.mul x.v6 x.v2) (UInt256.ofNat 23)),
    x.v1,
    (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.shiftRight (UInt256.mul x.v6 (UInt256.land x.v7 (UInt256.add x.v1 (UInt256.add (PadValues.load n 162) (UInt256.add (UInt256.xor x.v3 (UInt256.lor x.v2 (UInt256.lnot x.v0))) x.v5))))) (UInt256.ofNat 24)))),
    x.v3,
    x.v4,
    x.v0,
    x.v6,
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12 ] ++ rho
def actualOutput (n : UInt256) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.shiftRight (UInt256.mul x.v6 x.v2) (UInt256.ofNat 23)),
    x.v1,
    (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.shiftRight (UInt256.mul x.v6 (UInt256.land x.v7 (UInt256.add x.v1 (UInt256.add (PadValues.load n 162) (UInt256.add (UInt256.xor x.v3 (UInt256.lor x.v2 (UInt256.lnot x.v0))) x.v5))))) (UInt256.ofNat 24)))),
    x.v3,
    x.v4,
    x.v0,
    x.v6,
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12 ] ++ rho
private theorem actualOutput_eq (n : UInt256) (x : Input) (rho : List UInt256) :
    actualOutput n x rho = outputStack n x rho := by rfl
private theorem run_generated (s : State) (pc n : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (halias : rho[2]? = some x.v2) (hkey : x.v1 = UInt256.ofNat 1352829926) (hcache : x.v5 = x.v12) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load n 162)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4601 = true) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := UInt256.ofNat 4638, stack := actualOutput n x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 48) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, actualOutput, hcal, hmem, hvalid, PadValues.load,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap, halias, hkey, hcache,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [PadValues.add_zero, PadValues.zero_add, neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.mulMod_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem run_actual (s : State) (pc n : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (halias : rho[2]? = some x.v2) (hkey : x.v1 = UInt256.ofNat 1352829926) (hcache : x.v5 = x.v12) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load n 162)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4601 = true) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := UInt256.ofNat 4638, stack := outputStack n x rho} := by
  simpa only [actualOutput_eq] using run_generated s pc n x rho hstack halias hkey hcache hrun hactive hcal hmem hvalid
#print axioms run_actual
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadRawRight1
