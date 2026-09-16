import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.JointRightPackRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
structure Input where
  rd : UInt256
  k : UInt256
  rb : UInt256
  rc : UInt256
  ra : UInt256
  re : UInt256
  factor : UInt256
  lower : UInt256
  cache140 : UInt256
  cache350 : UInt256
  cache310 : UInt256
  cache190 : UInt256
  h4 : UInt256
  h1 : UInt256
  h2 : UInt256
  h3 : UInt256
  h0 : UInt256
  off : UInt256
  limit : UInt256
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
def template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .NOT,
    .op .OR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 252),
    .op .MLOAD,
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
    .op (.Dup ⟨7, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op .OR ]

def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.rd, x.k, x.rb, x.rc, x.ra, x.re, x.factor, x.lower, x.cache140, x.cache350, x.cache310, x.cache190, x.h4, x.h3, x.h2, x.h1, x.h0, x.off, x.limit ] ++ rho
def actualOutput (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.lor (UInt256.shiftLeft x.lower (UInt256.ofNat 144)) x.lower),
    (UInt256.shiftLeft x.lower (UInt256.ofNat 144)),
    (UInt256.lor x.h4 (UInt256.shiftLeft x.rd (UInt256.ofNat 144))),
    (UInt256.lor x.h1 (UInt256.shiftLeft (UInt256.land x.lower (UInt256.add x.re (UInt256.shiftRight (UInt256.mul x.factor (UInt256.land x.lower (UInt256.add (UInt256.add (MachineState.readWord memory 252) (UInt256.add (UInt256.xor x.rb (UInt256.lor x.rc (UInt256.lnot x.rd))) x.ra)) x.k))) (UInt256.ofNat 24)))) (UInt256.ofNat 144))),
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
def rotatedC (x : Input) : UInt256 :=
  UInt256.shiftRight (UInt256.mul x.factor x.rc) (UInt256.ofNat 23)
def roundT (memory : ByteArray) (x : Input) : UInt256 :=
  UInt256.land x.lower (UInt256.add x.re
    (UInt256.shiftRight (UInt256.mul x.factor
      (UInt256.land x.lower (UInt256.add x.k
        (UInt256.add (MachineState.readWord memory 252)
          (UInt256.add (UInt256.xor (UInt256.lor x.rc (UInt256.lnot x.rd)) x.rb) x.ra)))))
      (UInt256.ofNat 24)))
def packed (a b : UInt256) : UInt256 :=
  UInt256.lor a (UInt256.shiftLeft b (UInt256.ofNat 144))
def upperMask : UInt256 := UInt256.ofNat ((2^32-1)*2^144)
def pairMask : UInt256 := UInt256.ofNat ((2^32-1)*(1+2^144))
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.lor x.lower (UInt256.shiftLeft x.lower (UInt256.ofNat 144))), (UInt256.shiftLeft x.lower (UInt256.ofNat 144)),
    packed x.h4 x.rd, packed x.h1 (roundT memory x), packed x.h0 x.re,
    packed x.h3 (rotatedC x), packed x.h2 x.rb,
    x.factor, x.lower, x.cache140, x.cache350, x.cache310, x.cache190,
    x.h4, x.h3, x.h2, x.h1, x.h0, x.off, x.limit ] ++ rho
private theorem actualOutput_eq (memory : ByteArray) (x : Input) (rho : List UInt256) :
    actualOutput memory x rho = outputStack memory x rho := by
  simp only [actualOutput, outputStack, packed, rotatedC, roundT, pairMask, upperMask,
    RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm,
    RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm,
    RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm,
    RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
private theorem run_generated (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hlower : x.lower = UInt256.ofNat 4294967295) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := actualOutput s.memory x rho} := by
  have hupper : UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 144) =
      UInt256.ofNat 95780971281817308448866066055358605703522833630494720 := by decide
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 32) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, actualOutput, hlower, hupper,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hlower : x.lower = UInt256.ofNat 4294967295) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  simpa only [actualOutput_eq] using run_generated s pc x rho hstack hrun hactive hlower
#print axioms run_actual
end Challenge.Ripemd160.Submission.Proofs.Bytecode.JointRightPackRaw
