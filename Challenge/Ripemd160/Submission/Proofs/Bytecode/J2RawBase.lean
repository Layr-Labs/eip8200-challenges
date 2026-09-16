import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionControlRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Accumulator

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence

private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl

structure Frame where
  acc : UInt256
  off : UInt256
  word : UInt256
  full : UInt256
  stop : UInt256
  len : UInt256

def c32 : UInt256 := UInt256.mul (UInt256.ofNat 32) PatternedSwar.M
def c114 : UInt256 := UInt256.mul (UInt256.ofNat 114) PatternedSwar.M
def frame (f : Frame) (rho : List UInt256) : List UInt256 :=
  [f.acc, f.off, f.word, f.full, f.stop, c114, c32,
    PatternedSwar.m7, PatternedSwar.m8, PatternedSwar.M] ++ rho

def clamp (x : UInt256) : UInt256 := UInt256.add x
  (UInt256.mul (UInt256.lt (UInt256.ofNat 251) x) (UInt256.sub (UInt256.ofNat 251) x))
def aligned (x : UInt256) : UInt256 := UInt256.land x (UInt256.lnot (UInt256.ofNat 31))
def initResult (n : Nat) : Frame :=
  ⟨0, 0, PatternedSwar.P, aligned (clamp (UInt256.ofNat n)),
    clamp (UInt256.ofNat n), UInt256.ofNat n⟩
def normalResult (s : State) (f : Frame) : Frame :=
  { f with
    acc := UInt256.lor (UInt256.xor (MachineState.readWord s.executionEnv.calldata f.off.toNat) f.word) f.acc
    off := UInt256.add (UInt256.ofNat 32) f.off
    word := advance 32 f.word }
def tailResult (s : State) (f : Frame) : Frame :=
  { f with
    acc := UInt256.lor
      (UInt256.shiftRight (UInt256.xor f.word (MachineState.readWord s.executionEnv.calldata f.off.toNat))
        (UInt256.sub (UInt256.ofNat 256) (UInt256.shiftLeft (UInt256.sub f.stop f.off) (UInt256.ofNat 3)))) f.acc }
def transitionResult (f : Frame) : Frame :=
  let e := UInt256.add f.stop (clamp (UInt256.sub f.len f.stop))
  { f with word := advance 114 f.word
           off := f.stop
           stop := e
           full := UInt256.add f.stop (aligned (UInt256.sub e f.stop)) }

/-! ### Masking with `0xE0` instead of `~0x1F`

`aligned x = x &&& ~0x1F` clears the low five bits of `x`.  Whenever `x < 256`
the high bits of `x` are already zero, so masking with the single byte `0xE0`
does the same job -- and `PUSH1 224; JUMPDEST` costs 4 gas where
`PUSH1 31; NOT` costs 6.

The `< 256` side condition is discharged from the *definition* of `clamp`, not
from any sample of calldata: `clamp x = x + (251 < x)·(251 - x)` is `min x 251`
by `clamp_lt` below, for every `x : UInt256` and hence for every calldata
length, including lengths at or above `2 ^ 61`. -/

theorem nat_and_e0 (m : Nat) (h : m < 256) : m &&& 224 = m &&& (2 ^ 256 - 32) := by
  interval_cases m <;> decide

theorem add_sub_self (a b : UInt256) : UInt256.add a (UInt256.sub b a) = b := by
  unfold UInt256.add UInt256.sub
  congr 1
  exact add_sub_cancel a.val b.val

theorem sub_add_self (a b : UInt256) : UInt256.sub (UInt256.add a b) a = b := by
  unfold UInt256.add UInt256.sub
  congr 1
  exact add_sub_cancel_left a.val b.val

theorem land224_eq_aligned (x : UInt256) (h : x.toNat < 256) :
    UInt256.land x (UInt256.ofNat 224) = aligned x := by
  unfold aligned UInt256.land
  congr 1
  apply Fin.ext
  show (x.val.val &&& 224) % 2 ^ 256 = (x.val.val &&& (2 ^ 256 - 32)) % 2 ^ 256
  rw [nat_and_e0 x.val.val h]

/-- `clamp` never exceeds 251, so its result always fits in a single byte. -/
theorem clamp_lt (x : UInt256) : (clamp x).toNat < 256 := by
  unfold clamp UInt256.lt
  split
  · next _ =>
    have h1 : UInt256.mul (UInt256.ofNat 1) (UInt256.sub (UInt256.ofNat 251) x)
        = UInt256.sub (UInt256.ofNat 251) x := by
      unfold UInt256.mul; congr 1; exact one_mul _
    rw [h1, add_sub_self]
    decide
  · next hle =>
    have h0 : UInt256.mul (UInt256.ofNat 0) (UInt256.sub (UInt256.ofNat 251) x)
        = UInt256.ofNat 0 := by
      unfold UInt256.mul; congr 1; exact zero_mul _
    have hx : UInt256.add x (UInt256.ofNat 0) = x := by
      unfold UInt256.add; congr 1; exact add_zero _
    rw [h0, hx]
    have h251 : (UInt256.ofNat 251).toNat = 251 := rfl
    rw [h251] at hle
    omega

/-- `initResult` with the `0xE0` mask in place of `~0x1F`.  The operand is left
in its unreduced form so that it still matches what the template's symbolic
execution produces. -/
theorem initResult_eq (n : Nat) : initResult n =
    ⟨0, 0, PatternedSwar.P,
      UInt256.land (clamp (UInt256.ofNat n)) (UInt256.ofNat 224),
      clamp (UInt256.ofNat n), UInt256.ofNat n⟩ := by
  rw [initResult, land224_eq_aligned _ (clamp_lt _)]

def initTemplate : List Instr := [
  .push ⟨1, by decide⟩ (UInt256.ofNat 255),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .NOT,
  .op .DIV,
  .op (.Dup ⟨0, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 7),
  .op .SHL,
  .op (.Dup ⟨0, by decide⟩),
  .op .NOT,
  .op (.Dup ⟨2, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 5),
  .op .SHL,
  .op (.Dup ⟨3, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 114),
  .op .MUL,
  .op .CALLDATASIZE,
  .op .CALLDATASIZE,
  .push ⟨2, by decide⟩ (UInt256.ofNat 251),
  .op .LT,
  .op .CALLDATASIZE,
  .push ⟨1, by decide⟩ (UInt256.ofNat 251),
  .op .SUB,
  .op .MUL,
  .op .ADD,
  .op (.Dup ⟨0, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 224),
  .op .AND,
  .push ⟨32, by decide⟩ (UInt256.ofNat 3244493450063667868678674439968361782956185527883176199882357678282131398018),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0)
]

def firstTemplate : List Instr := [ .op (.Dup ⟨3, by decide⟩),
    .op .ISZERO,
    .push ⟨1, by decide⟩ (UInt256.ofNat 214),
    .op .JUMPI ]

def normalTemplate : List Instr := [
  .op .JUMPDEST,
  .op (.Dup ⟨2, by decide⟩),
  .op (.Dup ⟨2, by decide⟩),
  .op .CALLDATALOAD,
  .op .XOR,
  .op .OR,
  .op (.Swap ⟨0, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 32),
  .op .ADD,
  .op (.Swap ⟨0, by decide⟩),
  .op (.Dup ⟨8, by decide⟩),
  .op (.Dup ⟨3, by decide⟩),
  .op .NOT,
  .op .AND,
  .op (.Dup ⟨8, by decide⟩),
  .op (.Dup ⟨4, by decide⟩),
  .op .AND,
  .op (.Dup ⟨8, by decide⟩),
  .op .ADD,
  .op .XOR,
  .op (.Swap ⟨2, by decide⟩),
  .op .POP]

def normalGuardTemplate : List Instr := [ .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op .LT,
    .push ⟨1, by decide⟩ (UInt256.ofNat 185),
    .op .JUMPI ]

def tailTemplate : List Instr := [
  .op .JUMPDEST,
  .op (.Dup ⟨1, by decide⟩),
  .op (.Dup ⟨5, by decide⟩),
  .op .SUB,
  .push ⟨1, by decide⟩ (UInt256.ofNat 3),
  .op .SHL,
  .push ⟨2, by decide⟩ (UInt256.ofNat 256),
  .op .SUB,
  .op (.Dup ⟨2, by decide⟩),
  .op .CALLDATALOAD,
  .op (.Dup ⟨4, by decide⟩),
  .op .XOR,
  .op (.Swap ⟨0, by decide⟩),
  .op .SHR,
  .op .OR]

def finishTemplate : List Instr := [ .op .CALLDATASIZE,
    .op (.Dup ⟨5, by decide⟩),
    .op .EQ,
    .push ⟨2, by decide⟩ (UInt256.ofNat 288),
    .op .JUMPI ]

def transitionTemplate : List Instr := [
  .op (.Dup ⟨8, by decide⟩),
  .op (.Dup ⟨3, by decide⟩),
  .op .NOT,
  .op .AND,
  .op (.Dup ⟨8, by decide⟩),
  .op (.Dup ⟨4, by decide⟩),
  .op .AND,
  .op (.Dup ⟨7, by decide⟩),
  .op .ADD,
  .op .XOR,
  .op (.Dup ⟨5, by decide⟩),
  .op (.Swap ⟨2, by decide⟩),
  .op .POP,
  .op (.Swap ⟨2, by decide⟩),
  .op .POP,
  .op (.Dup ⟨1, by decide⟩),
  .op .CALLDATASIZE,
  .op .SUB,
  .op (.Dup ⟨0, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 251),
  .op .LT,
  .op (.Dup ⟨1, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 251),
  .op .SUB,
  .op .MUL,
  .op .ADD,
  .op (.Dup ⟨2, by decide⟩),
  .op .ADD,
  .op (.Swap ⟨4, by decide⟩),
  .op (.Dup ⟨5, by decide⟩),
  .op .SUB,
  .push ⟨1, by decide⟩ (UInt256.ofNat 224),
  .op .AND,
  .op (.Dup ⟨2, by decide⟩),
  .op .ADD,
  .op (.Swap ⟨3, by decide⟩),
  .op .POP
]

def transitionGuardTemplate : List Instr := [ .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op .LT,
    .push ⟨1, by decide⟩ (UInt256.ofNat 185),
    .op .JUMPI ]

def toTailTemplate : List Instr := [ .push ⟨1, by decide⟩ (UInt256.ofNat 214),
    .op .JUMP ]

def resultTemplate : List Instr := [ .op .JUMPDEST,
    .push ⟨2, by decide⟩ (UInt256.ofNat 330),
    .op .JUMPI ]


end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
