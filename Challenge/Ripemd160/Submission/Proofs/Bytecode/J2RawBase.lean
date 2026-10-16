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
  /-- Ghost global full-word limit; never serialized or read by the raw scanner. -/
  full : UInt256
  stop : UInt256
  len : UInt256

def c96 : UInt256 := UInt256.mul (UInt256.ofNat 96) PatternedSwar.M
def m9f : UInt256 := UInt256.ofNat 0x9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f9f
def c114 : UInt256 := UInt256.mul (UInt256.ofNat 114) PatternedSwar.M
def frame (f : Frame) (rho : List UInt256) : List UInt256 :=
  [f.acc, f.off, f.word,
    f.stop] ++ rho

def clamp (x : UInt256) : UInt256 := UInt256.add x
  (UInt256.mul (UInt256.lt (UInt256.ofNat 251) x) (UInt256.sub (UInt256.ofNat 251) x))
def aligned (x : UInt256) : UInt256 := UInt256.land x (UInt256.lnot (UInt256.ofNat 31))
def initResult (n : Nat) : Frame :=
  ⟨0, 0, PatternedSwar.P, UInt256.sub (UInt256.ofNat n) (UInt256.ofNat 32),
    clamp (UInt256.ofNat n), UInt256.ofNat n⟩
/-- One in-segment SWAR step (`+0xa0` bytewise) in the form the loop computes it:
`u = w ||| 0x9f..9f`, `w' = w ^^^ ((u - 0x60..60) ^^^ u)` (`0x60..60 = ~0x9f..9f`).  Agrees with `advance 32` on every
pattern word used by the recogniser (`J2Frame.nw_next`, by `decide`). -/
def nw (w : UInt256) : UInt256 :=
  UInt256.xor w (UInt256.xor (UInt256.sub (UInt256.lor w m9f) c96)
    (UInt256.lor w m9f))
def normalResult (s : State) (f : Frame) : Frame :=
  { f with
    acc := UInt256.lor (UInt256.xor (MachineState.readWord s.executionEnv.calldata f.off.toNat) f.word) f.acc
    off := UInt256.add (UInt256.ofNat 32) f.off
    word := nw f.word }
def tailResult (s : State) (f : Frame) : Frame :=
  { f with
    acc := UInt256.lor
      (UInt256.shiftRight (UInt256.xor f.word (MachineState.readWord s.executionEnv.calldata f.off.toNat))
        (if f.stop.toNat < f.len.toNat then UInt256.ofNat 40
          else UInt256.shiftLeft
              (UInt256.add (UInt256.sub f.off f.len) (UInt256.ofNat 32)) (UInt256.ofNat 3))) f.acc }
/-- Legacy segment end, in the exact shape the old transition template computes
(`PUSH1 251 DUP6 ADD DUP1 CALLDATASIZE SUB DUP1 CALLDATASIZE SAR AND ADD`): with `x = stop + 251` and
`d = len - x`, it is `x + (d &&& (d sar len))`.  Transitions only happen on the long lengths
(`len ≥ 256`), where `d sar len` is the sign mask of `d`, so this is `min x len`; the frame facts
check it by `decide` at every transition point (`J2Frame.Facts`). -/
def emin (stop len : UInt256) : UInt256 :=
  UInt256.add (UInt256.land (UInt256.sub len (UInt256.add (UInt256.ofNat 251) stop))
      (UInt256.sar (UInt256.sub len (UInt256.add (UInt256.ofNat 251) stop)) len))
    (UInt256.add (UInt256.ofNat 251) stop)
/-- Segment-boundary SWAR step (`+0xf2` bytewise) as the bytecode computes it:
`u = w ||| (c96 << 2)`, `w'' = w ^^^ ((u - 0x0e..0e) ^^^ u)`; the bytecode
derives the additive inverse of `0x0e..0e` as `(c96 << 2) SDIV 9`.
The signed-division and modular-addition identities are proved for all input words
in `J2RawTransition`, not assumed from scorer vectors. The shifted sentinel has
bytes 0x81 except for its least-significant byte 0x80; the extra low bits
do not affect this even bytewise subtraction.  Agrees with `advance 114` on the
pattern words where a segment ends (`J2Frame.tw_next`, by `decide`). -/
def tw (w : UInt256) : UInt256 :=
  UInt256.xor w (UInt256.xor
    (UInt256.sub (UInt256.lor w (UInt256.shiftLeft c96 (UInt256.ofNat 2)))
      (UInt256.mul (UInt256.ofNat 14) PatternedSwar.M))
    (UInt256.lor w (UInt256.shiftLeft c96 (UInt256.ofNat 2))))

/-- The hoisted branch selects the exact next stop, without a saturation step. -/
def transitionStop (f : Frame) : UInt256 :=
  if UInt256.land f.len (UInt256.ofNat 16) = 0 then UInt256.add (UInt256.ofNat 251) f.stop
  else f.len

/-- Raw result of the current hoisted transition. Both branches preserve the
ghost global full-word limit established by initialization. -/
def transitionResult (f : Frame) : Frame :=
  { f with word := tw f.word
           off := f.stop
           stop := transitionStop f }

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

/-- Explicit initialization result. The global full-word limit is a ghost;
only `acc`, `off`, `word` and `stop` contribute to serialization. -/
theorem initResult_eq (n : Nat) : initResult n =
    ⟨0, 0, PatternedSwar.P,
      UInt256.sub (UInt256.ofNat n) (UInt256.ofNat 32),
      clamp (UInt256.ofNat n), UInt256.ofNat n⟩ := rfl

def initTemplate : List Instr := [
  .push ⟨32, by decide⟩ (UInt256.ofNat 3244493450063667868678674439968361782956185527883176199882357678282131398018),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0)
]


/-- The scanner's word chain: seven copies of `normalTemplate` at `4970 + 82 j` (`j < 7`), falling into the
tail at `5544 = 4970 + 82 * 7`. A segment with `m` full words enters at block `7 - m`, so no per-word bound test
runs. The entry is the computed jump `5544 + 82 * ((x - full) sar 5)`, where `x` is the segment's first offset;
for `full = x + len - 32` this is `5544 - 82 * ceil ((len - 32) / 32)`. -/
def dispatchTarget (x full : UInt256) : UInt256 :=
  UInt256.add (UInt256.ofNat 5544)
    (UInt256.mul (UInt256.ofNat 82) (UInt256.sar (UInt256.sub x full) (UInt256.ofNat 5)))

/-- Block `j` of the chain; block 7 is the tail. -/
def blockPC (j : Nat) : Nat := 4970 + 82 * j

/-- First dispatch uses the clamped stop independently of the global full-word limit. -/
def firstTarget (stop : UInt256) : UInt256 :=
  dispatchTarget (UInt256.ofNat 0) (UInt256.sub stop (UInt256.ofNat 32))

/-- The new entry computes `32 - stop = 0 - (stop - 32)` in word arithmetic. -/
theorem sub32_stop (stop : UInt256) :
    UInt256.sub (UInt256.ofNat 32) stop =
      UInt256.sub (UInt256.ofNat 0) (UInt256.sub stop (UInt256.ofNat 32)) := by
  unfold UInt256.sub
  congr 1
  change (UInt256.ofNat 32).val - stop.val = 0 - (stop.val - (UInt256.ofNat 32).val)
  simp only [zero_sub, neg_sub]

/-- First entry duplicates the saved stop and reads the one-word memory size. -/
def dispatch0Template : List Instr := [ .op (.Dup ⟨3, by decide⟩),
    .op .MSIZE,
    .op .SUB,
    .push ⟨1, by decide⟩ (UInt256.ofNat 5),
    .op .SAR,
    .push ⟨1, by decide⟩ (UInt256.ofNat 82),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 5544),
    .op .ADD,
    .op .JUMP ]

/-- The hoisted transition selects either the first or fourth normal block. -/
def transitionTarget (n : UInt256) : UInt256 :=
  if UInt256.land n (UInt256.ofNat 16) = 0 then UInt256.ofNat (blockPC 0)
  else UInt256.ofNat (blockPC 4)

/-- Increment the saved offset before loading the old offset. This eliminates one
swap while preserving the exact incoming and outgoing recognizer frames. The
increment uses MSIZE while exactly one memory word is active. -/
def normalTemplate : List Instr := [
  .op .JUMPDEST,
  .op (.Dup ⟨1, by decide⟩),
  .op .MSIZE,
  .op .ADD,
  .op (.Swap ⟨1, by decide⟩),
  .op .CALLDATALOAD,
  .push ⟨32, by decide⟩ m9f,
  .op (.Dup ⟨4, by decide⟩),
  .op .OR,
  .push ⟨32, by decide⟩ c96,
  .op (.Dup ⟨1, by decide⟩),
  .op .SUB,
  .op .XOR,
  .op (.Dup ⟨4, by decide⟩),
  .op .XOR,
  .op (.Swap ⟨3, by decide⟩),
  .op .XOR,
  .op .OR]

/-- A tail's XOR remains live until the segment-length branch. -/
def tailDiff (s : State) (f : Frame) : UInt256 :=
  UInt256.xor f.word (MachineState.readWord s.executionEnv.calldata f.off.toNat)
def pending (s : State) (f : Frame) (rho : List UInt256) : List UInt256 :=
  tailDiff s f :: frame f rho

def tailTemplate : List Instr := [
  .op .JUMPDEST, .op (.Dup ⟨1, by decide⟩), .op .CALLDATALOAD,
  .op (.Dup ⟨3, by decide⟩), .op .XOR]

def finishTemplate : List Instr := [ .op .CALLDATASIZE,
    .op (.Dup ⟨5, by decide⟩), .op .LT,
    .push ⟨2, by decide⟩ (UInt256.ofNat 4853), .op .JUMPI ]

def finalProjectionTemplate : List Instr := [
  .op .CALLDATASIZE, .op (.Dup ⟨3, by decide⟩), .op .SUB,
  .op .MSIZE, .op .ADD,
  .push ⟨1, by decide⟩ (UInt256.ofNat 3), .op .SHL, .op .SHR, .op .OR]

def boundaryProjectionTemplate : List Instr := [
  .op .JUMPDEST, .push ⟨1, by decide⟩ (UInt256.ofNat 40), .op .SHR, .op .OR]

def resultTemplate : List Instr := [ .push ⟨2, by decide⟩ (UInt256.ofNat 4785),
    .op .JUMPI ]


end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
