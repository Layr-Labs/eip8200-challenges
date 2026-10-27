import Challenge.Ripemd160.Submission.Proofs.Bytecode.JointRightPackRaw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawPack
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.JointRightPackRaw (inputStack outputStack)
open Challenge.Ripemd160.Submission.Proofs.Bytecode.JointRightPackRaw (Input)
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem hmul_eq_mul (x y : UInt256) : x * y = UInt256.mul x y := rfl
private theorem hadd_eq_add (x y : UInt256) : x + y = UInt256.add x y := rfl
private theorem zero_hadd (a : UInt256) : UInt256.add (UInt256.ofNat 0) a = a := by
  apply Word.word_ext; cases a; simp [UInt256.add, UInt256.ofNat, UInt256.toNat]
private theorem hadd_zero (a : UInt256) : UInt256.add a (UInt256.ofNat 0) = a := by
  apply Word.word_ext; cases a; simp [UInt256.add, UInt256.ofNat, UInt256.toNat]
def template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .NOT,
    .op .OR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op (.Dup ⟨14, by decide⟩),
    .op .OR,
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op (.Dup ⟨13, by decide⟩),
    .op .OR,
    .op (.Swap ⟨3, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op (.Dup ⟨15, by decide⟩),
    .op .OR,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 23),
    .op .SHR,
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op (.Dup ⟨12, by decide⟩),
    .op .OR,
    .op (.Swap ⟨2, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .push ⟨22, by decide⟩ (UInt256.ofNat 95780971281817308448866066055358605703522833630494720),
    .push ⟨22, by decide⟩ (UInt256.ofNat 95780971281817308448866066055358605703522837925462015) ]
def padActual (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.lor (UInt256.ofNat 95780971281817308448866066055358605703522833630494720) x.lower),
    (UInt256.ofNat 95780971281817308448866066055358605703522833630494720),
    (UInt256.lor x.h4 (UInt256.shiftLeft x.rd (UInt256.ofNat 144))),
    (UInt256.lor x.h1 (UInt256.shiftLeft (UInt256.land x.lower (UInt256.add x.re (UInt256.shiftRight (UInt256.mul x.factor (UInt256.land x.lower (UInt256.add (UInt256.add (UInt256.ofNat 0) (UInt256.add (UInt256.xor x.rb (UInt256.lor x.rc (UInt256.lnot x.rd))) x.ra)) x.k))) (UInt256.ofNat 24)))) (UInt256.ofNat 144))),
    (UInt256.lor x.h0 (UInt256.shiftLeft x.re (UInt256.ofNat 144))),
    (UInt256.lor x.h3 (UInt256.shiftLeft (UInt256.shiftRight (UInt256.mul x.factor x.rc) (UInt256.ofNat 23)) (UInt256.ofNat 144))),
    (UInt256.lor x.h2 (UInt256.shiftLeft x.rb (UInt256.ofNat 144))),
    x.factor,
    x.lower,
    x.cache140,
    x.cache350,
    x.cache310,
    x.cache190,
    x.h4,
    x.h3,
    x.h2,
    x.h1,
    x.h0,
    x.off,
    x.limit ] ++ rho
private theorem run_generated (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hlower : x.lower = UInt256.ofNat 4294967295) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := padActual s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 32) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, padActual, zero_hadd, hadd_zero,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals try simp only [neutral_hadd, neutral_hmul, zero_hadd, hadd_zero, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl | (rw [hlower]; decide)
theorem out_eq (memory : ByteArray) (x : Input) (rho : List UInt256) (hz0 : MachineState.readWord memory 252 = UInt256.ofNat 0) :
    outputStack memory x rho = padActual memory x rho := by
  simp only [Challenge.Ripemd160.Submission.Proofs.Bytecode.JointRightPackRaw.outputStack, padActual, hz0, zero_hadd, hadd_zero, RawExpressionAC.add_assoc, RawExpressionAC.add_comm,
    JointRightPackRaw.packed, JointRightPackRaw.rotatedC, JointRightPackRaw.roundT, JointRightPackRaw.pairMask, JointRightPackRaw.upperMask, Nat.reducePow, Nat.reduceSub, Nat.reduceMul,
    RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm,
    RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm,
    RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm,
    RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm,
    RawExpressionAC.xor_left_comm, RawExpressionAC.mulMod_comm]
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hlower : x.lower = UInt256.ofNat 4294967295) (hz0 : MachineState.readWord s.memory 252 = UInt256.ofNat 0) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  rw [out_eq s.memory x rho hz0]
  exact run_generated s pc x rho hstack hrun hactive hlower
#print axioms run_actual
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawPack
