import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawRight0
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawRight0
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawRight0 (inputStack outputStack)
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem hmul_eq_mul (x y : UInt256) : x * y = UInt256.mul x y := rfl
private theorem hadd_eq_add (x y : UInt256) : x + y = UInt256.add x y := rfl
private theorem zero_hadd (a : UInt256) : UInt256.add (UInt256.ofNat 0) a = a := by
  apply Word.word_ext; cases a; simp [UInt256.add, UInt256.ofNat, UInt256.toNat]
private theorem hadd_zero (a : UInt256) : UInt256.add a (UInt256.ofNat 0) = a := by
  apply Word.word_ext; cases a; simp [UInt256.add, UInt256.ofNat, UInt256.toNat]
def template : List Instr :=
  [ .op (.Dup ⟨8, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 23),
    .op .SHR,
    .op (.Dup ⟨8, by decide⟩),
    .op (.Dup ⟨8, by decide⟩),
    .op (.Dup ⟨13, by decide⟩),
    .push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
    .op .ADD,
    .op (.Dup ⟨13, by decide⟩),
    .op (.Dup ⟨13, by decide⟩),
    .op (.Dup ⟨13, by decide⟩),
    .op .NOT,
    .op .OR,
    .op .XOR,
    .op .ADD,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op (.Dup ⟨4, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 25),
    .op .SHR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND ]
def padActual (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [     (UInt256.land x.v7 (UInt256.add x.v5 (UInt256.shiftRight (UInt256.mul x.v6 (UInt256.land x.v7 (UInt256.add x.v0 (UInt256.add (UInt256.add (UInt256.xor x.v2 (UInt256.lor x.v3 (UInt256.lnot x.v4))) (UInt256.ofNat 0)) x.v1)))) (UInt256.ofNat 25)))),
    x.v4,
    (UInt256.shiftRight (UInt256.mul x.v6 x.v3) (UInt256.ofNat 23)),
    x.v6,
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12 ] ++ rho
private theorem run_generated (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (halias : rho[2]? = some x.v2) (haliasC : rho[1]? = some x.v3) (haliasD : rho[0]? = some x.v4) (haliasA : rho[3]? = some x.v1) (hkey : x.v0 = UInt256.ofNat 1352829926) (haliasE : x.v12 = x.v5) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := padActual s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 48) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, padActual, zero_hadd, hadd_zero,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap, halias, haliasC, haliasD, haliasA, hkey, haliasE,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals try simp only [neutral_hadd, neutral_hmul, zero_hadd, hadd_zero, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.mulMod_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem out_eq (memory : ByteArray) (x : Input) (rho : List UInt256) (hz0 : MachineState.readWord memory 486 = UInt256.ofNat 0) :
    outputStack memory x rho = padActual memory x rho := by
  simp only [Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawRight0.outputStack, padActual, hz0, zero_hadd, hadd_zero, RawExpressionAC.add_assoc, RawExpressionAC.add_comm,
    RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm,
    RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm,
    RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm,
    RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm,
    RawExpressionAC.xor_left_comm, RawExpressionAC.mulMod_comm]
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (halias : rho[2]? = some x.v2) (haliasC : rho[1]? = some x.v3) (haliasD : rho[0]? = some x.v4) (haliasA : rho[3]? = some x.v1) (hkey : x.v0 = UInt256.ofNat 1352829926) (haliasE : x.v12 = x.v5) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hz0 : MachineState.readWord s.memory 486 = UInt256.ofNat 0) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  rw [out_eq s.memory x rho hz0]
  exact run_generated s pc x rho hstack halias haliasC haliasD haliasA hkey haliasE hrun hactive
#print axioms run_actual
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawRight0
