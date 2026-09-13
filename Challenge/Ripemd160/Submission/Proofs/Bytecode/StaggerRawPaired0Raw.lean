import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired0
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
def template : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 360),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 23),
    .push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op (.Swap ⟨6, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨11, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .XOR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 54),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op (.Dup ⟨10, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op (.Swap ⟨8, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .MUL,
    .op (.Dup ⟨1, by decide⟩),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0,
    x.v1,
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
    x.v13 ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land x.v0 (UInt256.shiftRight (UInt256.mul x.v7 x.v6) (UInt256.ofNat 23))),
    (UInt256.ofNat 23),
    (MachineState.readWord memory 360),
    x.v0,
    x.v1,
    x.v2,
    x.v3,
    (UInt256.ofNat 30169115476673038213297653277143730720156734734729216),
    x.v5,
    (UInt256.land x.v0 (UInt256.add x.v2 (UInt256.shiftRight (UInt256.mul x.v7 (UInt256.land x.v0 (UInt256.add (UInt256.ofNat 30169115476673038213297653277143730720156734734729216) (UInt256.add (MachineState.readWord memory 54) (UInt256.add (UInt256.xor (UInt256.xor (UInt256.lor x.v5 (UInt256.land x.v1 x.v6)) (UInt256.xor x.v6 x.v1)) x.v3) x.v4))))) (UInt256.ofNat 22)))),
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12,
    x.v13 ] ++ rho
def actualOutput (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land x.v0 (UInt256.shiftRight (UInt256.mul x.v7 x.v6) (UInt256.ofNat 23))),
    (UInt256.ofNat 23),
    (MachineState.readWord memory 360),
    x.v0,
    x.v1,
    x.v2,
    x.v3,
    (UInt256.ofNat 30169115476673038213297653277143730720156734734729216),
    x.v5,
    (UInt256.land x.v0 (UInt256.add x.v2 (UInt256.shiftRight (UInt256.mul x.v7 (UInt256.land x.v0 (UInt256.add (UInt256.ofNat 30169115476673038213297653277143730720156734734729216) (UInt256.add (MachineState.readWord memory 54) (UInt256.add (UInt256.xor (UInt256.xor (UInt256.lor x.v5 (UInt256.land x.v1 x.v6)) (UInt256.xor x.v6 x.v1)) x.v3) x.v4))))) (UInt256.ofNat 22)))),
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12,
    x.v13 ] ++ rho
private theorem actualOutput_eq (memory : ByteArray) (x : Input) (rho : List UInt256) :
    actualOutput memory x rho = outputStack memory x rho := by rfl
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired0
