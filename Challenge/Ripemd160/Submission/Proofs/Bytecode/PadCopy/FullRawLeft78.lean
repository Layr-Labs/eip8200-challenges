import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawLeft78
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawLeft78
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawLeft78 (inputStack outputStack)
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem zero_hadd (a : UInt256) : UInt256.add (UInt256.ofNat 0) a = a := by
  apply Word.word_ext; cases a; simp [UInt256.add, UInt256.ofNat, UInt256.toNat]
private theorem hadd_zero (a : UInt256) : UInt256.add a (UInt256.ofNat 0) = a := by
  apply Word.word_ext; cases a; simp [UInt256.add, UInt256.ofNat, UInt256.toNat]
private theorem zero_hadd' (a : UInt256) : UInt256.add {val := 0} a = a := zero_hadd a
private theorem hadd_zero' (a : UInt256) : UInt256.add a {val := 0} = a := hadd_zero a
/-- The zero-word placeholder `PUSH0` and the `ADD` that consumed it are
`JUMPDEST`s; the four `DUP`s between them each reach one slot less deep. -/
def template : List Instr :=
  [ .op .JUMPDEST,
    .op (.Dup ⟨10, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨13, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op .NOT,
    .op .OR,
    .op .XOR,
    .op .ADD,
    .op .JUMPDEST,
    .op (.Dup ⟨8, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨14, by decide⟩),
    .op .AND,
    .op (.Dup ⟨13, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 28),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨12, by decide⟩),
    .op (.Dup ⟨14, by decide⟩),
    .op .MUL,
    .op (.Dup ⟨11, by decide⟩),
    .op .SHR ]
def padActual (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.shiftRight (UInt256.mul x.v12 x.v11) (UInt256.ofNat 23)),
    (UInt256.add x.v2 (UInt256.shiftRight (UInt256.mul x.v12 (UInt256.land x.v13 (UInt256.add x.v7 (UInt256.add (UInt256.xor (UInt256.lor (UInt256.lnot x.v1) x.v11) x.v0) x.v10)))) (UInt256.ofNat 28))),
    x.v0,
    x.v1,
    x.v2,
    x.v3,
    (UInt256.ofNat 0),
    x.v5,
    x.v6,
    x.v7,
    x.v8,
    (UInt256.ofNat 23),
    x.v10,
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16,
    x.v17,
    x.v18 ] ++ rho
private theorem run_generated (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hz612 : MachineState.readWord s.memory 612 = UInt256.ofNat 0) (hc4 : x.v4 = UInt256.ofNat 0) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := padActual s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 48) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [zero_hadd, hadd_zero, zero_hadd', hadd_zero', hz612, hc4, template, inputStack, padActual,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [zero_hadd, hadd_zero, zero_hadd', hadd_zero', neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
  all_goals first | assumption | trivial | (simp only [zero_hadd', hadd_zero', zero_hadd, hadd_zero])
theorem out_eq (memory : ByteArray) (x : Input) (rho : List UInt256) (hz612 : MachineState.readWord memory 612 = UInt256.ofNat 0) (hc4 : x.v4 = UInt256.ofNat 0) :
    outputStack memory x rho = padActual memory x rho := by
  simp only [Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawLeft78.outputStack, padActual, hz612, hc4, zero_hadd, hadd_zero, RawExpressionAC.add_assoc, RawExpressionAC.add_comm,
    RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm,
    RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm,
    RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm,
    RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm,
    RawExpressionAC.xor_left_comm, RawExpressionAC.mulMod_comm]
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hz612 : MachineState.readWord s.memory 612 = UInt256.ofNat 0) (hc4 : x.v4 = UInt256.ofNat 0) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  rw [out_eq s.memory x rho hz612 hc4]
  exact run_generated s pc x rho hstack hrun hactive hz612 hc4
#print axioms run_actual
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawLeft78
