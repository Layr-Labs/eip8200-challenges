import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.Csub
import Challenge.Modexp.Submission.Proofs.Fast.FiosPC
import Challenge.Modexp.Submission.Proofs.Fast.FiosBlocks

/-
FiosRun.lean -- the value model, states, block reductions and loop certificates for
`artifact/fios-k9.hex`.  Supersedes FiosEvm.lean sections 2-5; keep that file as the
design note.

THE MAIN FINDING, and it makes this whole layer small:

  The engine's fused body is LITERALLY TWO OF `Monpro`'s EXISTING MAC STEPS.
  `Monpro.lean` already says "Both CIOS limb loops execute the same instruction
  sequence" and gives

      Monpro.mulHi   x y     = UInt256.mulMod x y maxWord - (x * y + lt (mulMod x y maxWord) (x * y))
      Monpro.macSum  x y t c = c + (t + x * y)
      Monpro.macCarry x y t c = lt (c + (t + x*y)) c + (lt (t + x*y) t + mulHi x y)
      Monpro.macSpec x y t c : (macCarry …).toNat * 2^256 + (macSum …).toNat
                                 = t.toNat + x.toNat * y.toNat + c.toNat

  I checked the TERM ORDER against the emitted opcodes, not just the value:
    * `MUL` pops the memory limb then the multiplier, so it is `x * y` with x the
      loaded limb -- `mulHi`'s own convention.
    * `t + x*y` and then `c + (t + x*y)` are the orders `add3` and `DUP4 ADD` produce.
    * `macCarry`'s two `lt`s are the `DUP3 LT` and `DUP4 LT` in that order.
  So the fused body is
      u  = macSum  b_j a_i t_j C1        C1' = macCarry b_j a_i t_j C1
      v  = macSum  N_j m   u   C2        C2' = macCarry N_j m   u   C2
  and NO new value function is needed anywhere.  `macSpec` applied twice is exactly
  `Fios.two_split` from FIOS_MATH.lean, one level down.

ADDRESSES -- all four verified against a running trace (n=4, pa=pb=5120, j=0,1,2):
      p_t   = 8224 + 32 * (n - j - 1)          reads t[j+1]
      p_b   = pa   + 32 * (n - j - 2)          reads b[j+1]
      p_n   =        32 * (n - j - 2)          reads N[j+1]
      store = 8256 + 32 * (n - j - 1)          writes t[j]

CONFIDENCE MARKERS: every step I am not certain of carries `-- ?N` and is listed at the
bottom.  Compile those first.
-/
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Fios


open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

/-! ## 1.  The peel, as the Row blocks compute it

`i` is the row index.  The row multiplier is limb `i` of the `pb` block; the peel reads
limb 0 of `pa`, `t` and `N`.  Nothing here uses `macSum`/`macCarry`, because the peel has
no carry-in and the block therefore emits `t + x*y` rather than `0 + (t + x*y)`. -/

def peelAi (mem : ByteArray) (pb n i : Nat) : UInt256 :=
  MachineState.readWord mem (pb + 32 * (n - 1 - i))

def peelB0 (mem : ByteArray) (pa n : Nat) : UInt256 :=
  MachineState.readWord mem (pa + 32 * (n - 1))

def peelT0 (mem : ByteArray) (n : Nat) : UInt256 :=
  MachineState.readWord mem (8224 + 32 * n)

def peelN0 (mem : ByteArray) (n : Nat) : UInt256 :=
  MachineState.readWord mem (32 * (n - 1))

/-- `S`, the low word after the peel's first accumulate. -/
def peelS (mem : ByteArray) (pa pb n i : Nat) : UInt256 :=
  peelT0 mem n + peelB0 mem pa n * peelAi mem pb n i

/-- The carry out of the peel's multiply step. -/
def peelC1 (mem : ByteArray) (pa pb n i : Nat) : UInt256 :=
  UInt256.lt (peelS mem pa pb n i) (peelT0 mem n)
    + Monpro.mulHi (peelB0 mem pa n) (peelAi mem pb n i)

/-- `m = n0inv * S`, truncated by `MUL`.  `V_MINV` is at 0x24A0 = 9376. -/
def peelM (mem : ByteArray) (pa pb n i : Nat) : UInt256 :=
  MachineState.readWord mem 9376 * peelS mem pa pb n i

/-- The carry out of the peel's reduce step.  Its low word is zero -- that is
`Fios.peelLow_eq_zero` on the arithmetic side -- and the block never stores it. -/
def peelC2 (mem : ByteArray) (pa pb n i : Nat) : UInt256 :=
  UInt256.gt (peelS mem pa pb n i)                                            -- ?1
      (peelS mem pa pb n i + peelN0 mem n * peelM mem pa pb n i)
    + Monpro.mulHi (peelN0 mem n) (peelM mem pa pb n i)

/-! ## 2.  The fused loop's workspace

`bodyW … j` is the pair of carries and the memory after `j` fused iterations of row `i`.
Shape copied from `Csub.amStep`. -/

structure BodyW where
  c1 : UInt256
  c2 : UInt256
  mem : ByteArray

def bodyW (mem : ByteArray) (pa pb n i : Nat) : Nat → BodyW
  | 0 => ⟨peelC1 mem pa pb n i, peelC2 mem pa pb n i, mem⟩
  | j + 1 =>
      let prev := bodyW mem pa pb n i j
      let ai := peelAi mem pb n i
      let m := peelM mem pa pb n i
      let tj := MachineState.readWord prev.mem (8224 + 32 * (n - j - 1))
      let bj := MachineState.readWord prev.mem (pa + 32 * (n - j - 2))
      let nj := MachineState.readWord prev.mem (32 * (n - j - 2))
      let u := Monpro.macSum bj ai tj prev.c1
      let v := Monpro.macSum nj m u prev.c2
      { c1 := Monpro.macCarry bj ai tj prev.c1
        c2 := Monpro.macCarry nj m u prev.c2
        mem := MachineState.writeBytes prev.mem
                 (Data.Bytes.natToBytesPadded v.toNat 32) (8256 + 32 * (n - j - 1)) }

/-- The `u` the first half of iteration `j` produces. -/
def bodyU (mem : ByteArray) (pa pb n i j : Nat) : UInt256 :=
  Monpro.macSum
    (MachineState.readWord (bodyW mem pa pb n i j).mem (pa + 32 * (n - j - 2)))
    (peelAi mem pb n i)
    (MachineState.readWord (bodyW mem pa pb n i j).mem (8224 + 32 * (n - j - 1)))
    (bodyW mem pa pb n i j).c1

/-! ## 3.  The row memory, and the whole-call memory

`rowsMem` mirrors `Monpro.rowsMem`; it is the ONLY component of `Subroutines.mpMem`
that changes. -/

def rowMem (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  let W := bodyW mem pa pb n i (n - 1)
  let x1 := MachineState.readWord W.mem (8224 + 32 * n - 32 * n) + W.c1        -- ?2
  let x2 := x1 + W.c2
  MachineState.writeBytes
    (MachineState.writeBytes W.mem (Data.Bytes.natToBytesPadded x2.toNat 32) 8256)
    (Data.Bytes.natToBytesPadded
      (UInt256.lt x1 W.c1 + UInt256.gt W.c2 x2).toNat 32) 8224                 -- ?1 ?3

def rowsMem (mem : ByteArray) (pa pb n : Nat) : Nat → ByteArray
  | 0 => mem     -- the CALLDATACOPY zeroing is applied by the CALLER, as
                 -- `Monpro.mpZeroed s mem n`, exactly as Monpro.rowsMem does
  | i + 1 => rowMem (rowsMem mem pa pb n i) pa pb n i

-- (`fiosMem` moved to FiosMem.lean as `Fios.monproMem`, defined through
--  `Monpro.monproMemOf rowsMem` so the five memory lemmas come by instantiation.)

/-! ## 4.  States, one per block boundary

`rowFrame` is the ten words live across the call, `bodyFrame` the fifteen live across
the fused loop.  Both pointers are `Csub.ptrAt` walks starting one step in, so
`Csub.ptrAt_succ` rewrites the block's `PUSH32 0xFF..FFE0; ADD` straight onto the family
term and every step stays `rfl`. -/

/-- `&b[0] - &t[0]` and `&N[0] - &t[0]`, as PLAIN NATS wrapped by `UInt256.ofNat`
rather than as `UInt256` subtractions.  This is the whole of the `?7` fix: with the
offsets in this form, `Word.ofNat_add_mod` turns the body's `p_t + dB` into

    UInt256.ofNat (Csub.ptrAt (8224 + 32 * n) (j + 1) + dBN pa n)

and the exact identity `ptrAt (8224+32n) (j+1) + dBN pa n = ptrAt (pa+32n) (j+2)`
(proved as `ptrAt_dB` below) makes that a `ptrAt` walk ON THE B ARRAY, whose base
`pa + 32*n <= 8192` satisfies `Csub.ptrAt_toNat`'s `hbase < 2 ^ 256`.  Landing on the
b array's own base is the point: the naive route left the base as
`8224 + 32*n + dBN pa n`, which carries a `+ 2 ^ 256` and is NOT `< 2 ^ 256`, so no
`ptrAt` lemma could ever have applied to it. -/
def dBN (pa n : Nat) : Nat := 2 ^ 256 + (pa + 32 * n - 32) - (8224 + 32 * n)

def dNN (n : Nat) : Nat := 2 ^ 256 + (32 * n - 32) - (8224 + 32 * n)

def dB (pa n : Nat) : UInt256 := UInt256.ofNat (dBN pa n)

def dN (n : Nat) : UInt256 := UInt256.ofNat (dNN n)

/-! ### Address lemmas — the real cause of Error 1

You were right that `ptrAt_mod` could not match, but the literal-vs-`2 ^ 256` mismatch is
only the surface. The deeper problem is that my rewrite produced the base
`8224 + 32*n + dBN pa n`, which is **not** `< 2 ^ 256` — `dBN` carries a `+ 2 ^ 256` to
model the wrap — so neither `ptrAt_mod` nor `ptrAt_toNat` could ever have applied to it.

The fix is to land on a `ptrAt` walk over the **b array itself**, whose base is
`pa + 32 * n ≤ 8192`. And that identity is exact over the naturals, not merely modular:

    ptrAt (8224 + 32*n) (j+1) + dBN pa n = ptrAt (pa + 32*n) (j+2)

  LHS = (8224+32n) + (j+1)·K + 2^256 + pa − 8256
  RHS = (pa+32n)   + (j+1)·K + K            with K = 2^256 − 32
  LHS − RHS = 8224 − 8256 + 2^256 − K = −32 + 32 = 0.

Verified against the trace: n=4, pa=5120, j=0 gives `ptrAt (5120+128) 2 = 5184`, which is
the p_b the interpreter shows. Then `Csub.ptrAt_toNat` applies with `base = pa + 32*n`,
and its `hbase < 2 ^ 256` is discharged by `hpaFit`. Same shape for `dN` at base `32*n`. -/

theorem ptrAt_dB (pa n j : Nat) (hpa : 32 ≤ pa) :
    Csub.ptrAt (8224 + 32 * n) (j + 1) + dBN pa n
      = Csub.ptrAt (pa + 32 * n) (j + 2) := by
  simp only [Csub.ptrAt, dBN]
  omega                                                                        -- ?H

theorem ptrAt_dN (n j : Nat) (hn2 : 2 ≤ n) :
    Csub.ptrAt (8224 + 32 * n) (j + 1) + dNN n
      = Csub.ptrAt (32 * n) (j + 2) := by
  simp only [Csub.ptrAt, dNN]
  omega                                                                        -- ?H

/-- `p_b` at fused iteration `j`, in the form the block leaves it. -/
theorem toNat_pb (pa n j : Nat) (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hj : j + 2 ≤ n) :
    (UInt256.ofNat (Csub.ptrAt (8224 + 32 * n) (j + 1)) + dB pa n).toNat
      = pa + 32 * (n - j - 2) := by
  rw [dB, Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_dB pa n j hpa,
    Csub.ptrAt_toNat (pa + 32 * n) (j + 2) (by omega) (by omega)]
  omega

/-- `p_n` at fused iteration `j`. -/
theorem toNat_pn (n j : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32) (hj : j + 2 ≤ n) :
    (UInt256.ofNat (Csub.ptrAt (8224 + 32 * n) (j + 1)) + dN n).toNat
      = 32 * (n - j - 2) := by
  rw [dN, Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_dN n j hn2,
    Csub.ptrAt_toNat (32 * n) (j + 2) (by omega) (by omega)]
  omega

/-- `p_t` at fused iteration `j`, for the `t` read and the `t[j-1]` store. -/
theorem toNat_pt (n j : Nat) (hn32 : n ≤ 32) (hj : j + 1 ≤ n) :
    (UInt256.ofNat (Csub.ptrAt (8224 + 32 * n) (j + 1))).toNat
      = 8224 + 32 * (n - j - 1) := by
  rw [Csub.ptrAt_toNat (8224 + 32 * n) (j + 1) (by omega) (by omega)]
  omega

/-! ### The address bridges, at the level the goal actually has

The residual goal from the first `run_BodyA` compile showed the problem exactly: the
address occurs as a bare `Nat` modular expression

    (dBN pa n + (8224 + 32 * n + (j + 1) * 115792…639904)) % 115792…639936

while `hbAddr` spoke about a `UInt256` addition through `.toNat`.  The two never meet.
So the bridges below are stated in the goal's own form, with the 78-digit literals, and
they go through `Csub.ptrAt_mod` — which is *also* stated with that literal modulus, so
the spellings match without normalising anything.

The content is the exact-over-the-naturals identity: adding the delta to a `p_t` walk
gives a walk on the target array's own base, whose `hbase < 2 ^ 256` is then discharged
from `hpaFit`.  Note the summand order — `dBN` on the LEFT — copied from the dump. -/

theorem bAddr_mod (pa n j : Nat) (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hj : j + 2 ≤ n) :
    (dBN pa n +
        (8224 + 32 * n +
          (j + 1) *
            115792089237316195423570985008687907853269984665640564039457584007913129639904)) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = pa + 32 * (n - j - 2) := by
  have h1 : dBN pa n +
      (8224 + 32 * n +
        (j + 1) *
          115792089237316195423570985008687907853269984665640564039457584007913129639904)
      = Csub.ptrAt (pa + 32 * n) (j + 2) := by
    simp only [Csub.ptrAt, dBN]
    omega
  rw [h1, Csub.ptrAt_mod (pa + 32 * n) (j + 2) (by omega) (by omega)]
  omega

theorem nAddr_mod (n j : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32) (hj : j + 2 ≤ n) :
    (dNN n +
        (8224 + 32 * n +
          (j + 1) *
            115792089237316195423570985008687907853269984665640564039457584007913129639904)) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * (n - j - 2) := by
  have h1 : dNN n +
      (8224 + 32 * n +
        (j + 1) *
          115792089237316195423570985008687907853269984665640564039457584007913129639904)
      = Csub.ptrAt (32 * n) (j + 2) := by
    simp only [Csub.ptrAt, dNN]
    omega
  rw [h1, Csub.ptrAt_mod (32 * n) (j + 2) (by omega) (by omega)]
  omega

theorem tAddr_mod (n j : Nat) (hn32 : n ≤ 32) (hj : j + 1 ≤ n) :
    (8224 + 32 * n +
        (j + 1) *
          115792089237316195423570985008687907853269984665640564039457584007913129639904) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8224 + 32 * (n - j - 1) := by
  have h1 : 8224 + 32 * n +
      (j + 1) *
        115792089237316195423570985008687907853269984665640564039457584007913129639904
      = Csub.ptrAt (8224 + 32 * n) (j + 1) := rfl
  rw [h1, Csub.ptrAt_mod (8224 + 32 * n) (j + 1) (by omega) (by omega)]
  omega

/-- The store address, `p_t + 32`, which the body writes at `t[j-1]`. -/
theorem storeAddr_mod (n j : Nat) (hn32 : n ≤ 32) (hj : j + 1 ≤ n) :
    (32 +
        (8224 + 32 * n +
          (j + 1) *
            115792089237316195423570985008687907853269984665640564039457584007913129639904)) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8256 + 32 * (n - j - 1) := by
  have h1 : 32 +
      (8224 + 32 * n +
        (j + 1) *
          115792089237316195423570985008687907853269984665640564039457584007913129639904)
      = Csub.ptrAt (8256 + 32 * n) (j + 1) := by
    simp only [Csub.ptrAt]
    omega
  rw [h1, Csub.ptrAt_mod (8256 + 32 * n) (j + 1) (by omega) (by omega)]
  omega



/-! ### The peel's two addresses, and the Setup block's two deltas

`run_Row1` failed on exactly the `bAddr_mod` problem in two new spellings, and because
`blkFiosRow1` is the peel these do not occur in any other Row block -- which is why
Row1's residual is not Row2/3/4's.  Both are `Csub.ptrAt` walks; the first is the
`dB` delta applied to `&t[0]`, the second the row pointer's own walk. -/

/-- `dB` fits in a word: it is `2 ^ 256 + pa - 8256`, and `pa ≤ 8128` here. -/
theorem dB_toNat (pa n : Nat) (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192) :
    (dB pa n).toNat = dBN pa n := by
  simp only [dB, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simp only [dBN]; omega)

/-- `&a[n-1] = &t[0] + dB`, the peel's `a` limb. -/
theorem aTopAddr_mod (pa n : Nat) (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hn2 : 2 ≤ n) :
    ((dB pa n).toNat + (8224 + 32 * n)) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = pa + 32 * (n - 1) := by
  rw [dB_toNat pa n hpa hpaFit]
  have h1 : dBN pa n + (8224 + 32 * n) = Csub.ptrAt (pa + 32 * n) 1 := by
    simp only [Csub.ptrAt, dBN]
    omega
  rw [h1, Csub.ptrAt_mod (pa + 32 * n) 1 (by omega) (by omega)]
  omega

/-- `&b[n-1-i]`, the row pointer at row `i`.  This is `rowFrame`'s head walked one
step per row, so the index is `i + 1` rather than the body's `j + 2`. -/
theorem bRowAddr_mod (pb n i : Nat) (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i < n) :
    (pb + 32 * n +
        (i + 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = pb + 32 * (n - 1 - i) := by
  have h1 : pb + 32 * n +
      (i + 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904
      = Csub.ptrAt (pb + 32 * n) (i + 1) := rfl
  rw [h1, Csub.ptrAt_mod (pb + 32 * n) (i + 1) (by omega) (by omega)]
  omega

/-! ### The pointer STEP, and the operand order the EVM emits

`PUSH32 (2 ^ 256 - 32); ADD` puts the constant on the LEFT: the machine builds
`K + base`, while `Csub.ptrAt` unfolds to `base + j * K`.  `run_Row4` reduced to exactly
that one commutation and nothing else.  Stated under `UInt256.ofNat` rather than over
bare `Nat` on purpose: a bare `K + ?x = ?x + K` would fire on `Csub.ptrAt_succ`'s own
left-hand side and stop the pointer walk from ever folding. -/
theorem ofNat_K_comm (x : Nat) :
    UInt256.ofNat (115792089237316195423570985008687907853269984665640564039457584007913129639904 + x) = UInt256.ofNat (x + 115792089237316195423570985008687907853269984665640564039457584007913129639904) := by
  rw [Nat.add_comm]

/-- `dN` fits in a word, so the `.toNat` the goal carries is the folded `dNN`.  `dB` had
this via `run_BodyA`'s simp set; `dN` did not, which is the whole of `run_Row3` and
`run_BodyC`: their goals kept `(dN n).toNat` where `nAddr_mod` speaks of `dNN n`. -/
theorem dN_toNat (n : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    (dN n).toNat = dNN n := by
  simp only [dN, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simp only [dNN]; omega)

/-- `&N[n-1] = &t[0] + dN`, the peel's `N` limb.  The `dN` twin of `aTopAddr_mod`. -/
theorem nTopAddr_mod (n : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    (dNN n + (8224 + 32 * n)) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * (n - 1) := by
  have h1 : dNN n + (8224 + 32 * n) = Csub.ptrAt (32 * n) 1 := by
    simp only [Csub.ptrAt, dNN]
    omega
  rw [h1, Csub.ptrAt_mod (32 * n) 1 (by omega) (by omega)]
  omega

/-- `p_t` AFTER `blkFiosBodyE`'s decrement, which is what its `JUMPI` compares against
`0x2020`.  Without this the branch condition never resolves, both arms of the `if`
survive into the goal, and the kernel walks the doubled term -- that is the
`deep recursion` on `run_BodyE_*`, not `bodyW` unfolding. -/
theorem tStepAddr_mod (n j : Nat) (hn32 : n ≤ 32) (hj : j + 2 ≤ n) :
    (115792089237316195423570985008687907853269984665640564039457584007913129639904 +
        (8224 + 32 * n +
          (j + 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904)) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8224 + 32 * (n - j - 2) := by
  have h1 : 115792089237316195423570985008687907853269984665640564039457584007913129639904 +
      (8224 + 32 * n + (j + 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904)
      = Csub.ptrAt (8224 + 32 * n) (j + 2) := by
    simp only [Csub.ptrAt]
    omega
  rw [h1, Csub.ptrAt_mod (8224 + 32 * n) (j + 2) (by omega) (by omega)]
  omega

/-! ### The Setup block's two deltas

`blkFiosSetup` forms `dB` and `dN` by wrapping subtraction -- `(&b[n-1]) - (&t[0])` is
negative over the naturals -- so `Word.ofNat_sub_ofNat`, which needs `b ≤ a`, cannot
apply in any spelling.  These go through `Word.word_toNat_sub`, whose statement is the
wrapping one, and `dBN` / `dNN` are DEFINED as that wrap, so the two sides meet. -/

theorem deltaB_eq (pa n : Nat) (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192) :
    UInt256.ofNat (115792089237316195423570985008687907853269984665640564039457584007913129639904 + (pa + 32 * n))
        - UInt256.ofNat (8224 + 32 * n)
      = UInt256.ofNat (dBN pa n) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat, dBN]
  omega

/-- The same, before `Word.ofNat_add_mod` has collapsed the addition.  Whichever normal
form simp lands on, one of the two fires. -/
theorem deltaB_eq' (pa n : Nat) (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192) :
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904
        + UInt256.ofNat (pa + 32 * n) - UInt256.ofNat (8224 + 32 * n)
      = UInt256.ofNat (dBN pa n) := by
  rw [Challenge.EvmProof.Word.ofNat_add_mod]
  exact deltaB_eq pa n hpa hpaFit

/-- One more `ptrAt` step, in the arrangement `PUSH32 K; ADD` leaves behind: the machine
puts the constant on the LEFT of the already-stepped pointer, while the next state names
the step count directly.  `K + (base + m*K) = base + (m+1)*K` over the naturals. -/
theorem ofNat_K_step (base m K : Nat) :
    UInt256.ofNat (K + (base + m * K)) = UInt256.ofNat (base + (m + 1) * K) := by
  congr 1
  ring


/-! ### The loop-EXIT addresses, stated at `n - 1`.

An index-normalising `have` and an index-parameterised bridge must be stated in the
SAME orientation or they cancel: `hix2 : n - 2 + 1 = n - 1` fires first, rewrites the
machine's `(n - 2 + 1) * K` to `(n - 1) * K`, and every bridge stated at `n - 2 + 1`
is then unmatchable. These three are stated at `n - 1` for that reason. -/

/-- `Csub.ptrAt_mod` with `ptrAt` pre-unfolded: the form the goals actually carry,
because `Csub.ptrAt` sits in every block's simp set.  Every address bridge in this file
is a one-line instance of it. -/
theorem ptrWalk_mod (base m : Nat) (hm : 32 * m ≤ base) (hb : base < 2 ^ 256) :
    (base + m * 115792089237316195423570985008687907853269984665640564039457584007913129639904) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = base - 32 * m := by
  have h1 : base + m * 115792089237316195423570985008687907853269984665640564039457584007913129639904
      = Csub.ptrAt base m := rfl
  rw [h1, Csub.ptrAt_mod base m hm hb]


/-- The loop-exit pointer: after the last decrement `p_t` is `&t[n] = 0x2020` exactly,
which is why `blkFiosBodyE`'s `JUMPI` falls through.  This is the term the condition
tests, and without it both arms survive into the goal and the kernel walks the doubled
term -- the `deep recursion`. -/
theorem tExitAddr_mod (n : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    (115792089237316195423570985008687907853269984665640564039457584007913129639904 +
        (8224 + 32 * n + (n - 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904)) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8224 := by
  have h1 : 115792089237316195423570985008687907853269984665640564039457584007913129639904 + (8224 + 32 * n + (n - 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904)
      = 8224 + 32 * n + n * 115792089237316195423570985008687907853269984665640564039457584007913129639904 := by omega
  rw [h1, ptrWalk_mod (8224 + 32 * n) n (by omega) (by omega)]
  omega

/-- `p_t` at the last iteration, before the decrement: `&t[n-1] = 0x2040`. -/
theorem tPrevAddr_mod (n : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    (8224 + 32 * n + (n - 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8256 := by
  rw [ptrWalk_mod (8224 + 32 * n) (n - 1) (by omega) (by omega)]
  omega

/-- The last iteration's store address, `p_t + 32 = 0x2060`. -/
theorem sPrevAddr_mod (n : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    (32 + (8224 + 32 * n + (n - 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904)) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8288 := by
  have h1 : 32 + (8224 + 32 * n + (n - 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904)
      = 8256 + 32 * n + (n - 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904 := by omega
  rw [h1, ptrWalk_mod (8256 + 32 * n) (n - 1) (by omega) (by omega)]
  omega

/-- `x + y < y` iff `x + y < x` for wrapping word addition: the same bit, but not
definitionally equal.  `emit_body` builds the FIRST mac step with `DUP4; LT` against
the accumulator, which is `Monpro.macCarry`'s orientation, and the SECOND with `add3`,
which compares against the added operand instead.  BodyD is the only block assembling
a second mac step, so it is the only one that meets the mismatch.  Both orientations
already exist: `Monpro.add_carry_split` is stated the machine's way and `Monpro.macSpec`
proves the accumulator's, so this is only the bridge between them. -/
theorem lt_add_symm (x y : UInt256) :
    UInt256.lt (x + y) y = UInt256.lt (x + y) x := by
  apply Challenge.EvmProof.Word.word_ext
  have h1 := Monpro.add_carry_split x y
  have h2 := Monpro.add_carry_split y x
  rw [Challenge.EvmProof.Word.word_add_comm y x] at h2
  omega

theorem deltaB_eq_comm (pa n : Nat) (hpa : 32 <= pa) (hpaFit : pa + 32 * n <= 8192) :
    UInt256.ofNat (pa + 32 * n + 115792089237316195423570985008687907853269984665640564039457584007913129639904)
        - UInt256.ofNat (8224 + 32 * n)
      = UInt256.ofNat (dBN pa n) := by
  have h : pa + 32 * n + 115792089237316195423570985008687907853269984665640564039457584007913129639904
      = 115792089237316195423570985008687907853269984665640564039457584007913129639904 + (pa + 32 * n) := by omega
  rw [h]; exact deltaB_eq pa n hpa hpaFit

theorem deltaN_eq (n : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    UInt256.ofNat (32 * n - 32) - UInt256.ofNat (8224 + 32 * n)
      = UInt256.ofNat (dNN n) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat, dNN]
  omega

/-- Adding a constant to a `ptrAt` walk is the same walk on a shifted base.  This is the
lemma that makes the address side of every body block go through. -/
theorem ptrAt_add_const (base j K : Nat) :
    Csub.ptrAt base j + K = Csub.ptrAt (base + K) j := by
  simp only [Csub.ptrAt]
  omega

def rowFrame (n pa pb : Nat) (pdst ret : UInt256) (rest : List UInt256) (i : Nat) :
    List UInt256 :=
  [UInt256.ofNat (Csub.ptrAt (pb + 32 * n) (i + 1)), dB pa n, dN n,
   UInt256.ofNat (8224 + 32 * n), UInt256.ofNat (Csub.ptrAt pb 1),
   UInt256.ofNat (32 * n), UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret]
    ++ rest

def bodyFrame (n pa pb : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (i j : Nat) (c1 c2 m ai : UInt256) : List UInt256 :=
  [UInt256.ofNat (Csub.ptrAt (8224 + 32 * n) (j + 1)), c1, c2, m, ai]
    ++ rowFrame n pa pb pdst ret rest i

/-! Entry is `Monpro.mpEntryState s mem pa pb pdst ret rest` (pc 1939); the stub block
carries us to pc 5351 with the stack unchanged.

CORRECTION, and it was mine: I wrote here that `blkFiosStub` was deleted because
"`blk1379` IS those three instructions and is the name the rest of the tree uses".
Naming someone else's block was the wrong call whether or not it happens to hold: in
the PRE-swap tree `blk1379` is the original 27-instruction prologue (pc 1939..1973,
`PUSH2 0x2480; MLOAD; ... CALLDATACOPY; ...`), and whether it still is depends on
whether `Paths/P7.lean` was regenerated alongside `Artifact.lean` -- which is not
something this file should depend on.  `blkFiosStub` is restored in `FiosBlocks.lean`,
byte-derived from the patched artifact: indices 1379..1381, pc 1939/1940/1943, bytes
5b 61 12 98 56 (`JUMPDEST; PUSH2 0x1298; JUMP`).  The index convention is the one every
other block here uses -- the one `FiosPC.lean` compiled green against -- and `fastPC10`
covers 1377..1416, so it is still the right table. -/

/-! ### Per-iteration values, named once

`fiosBodyA..D` were referenced by the wrappers and never defined — Finding 2.  Defining
them needs the body's intermediate values named, so those come first.  Naming them also
fixed a second bug I had not seen: `fiosBody` was calling `bodyW (rowsMem …) n pa pb i j`
with the OLD argument order, after I realigned `bodyW` to `(mem) (pa pb n i)` to fit
`monproMemOf`.  It would have typechecked wrongly or not at all.

Everything below reads from `rowsMem mem pa pb n i`, the memory row `i` starts from. -/

def memAt (mem : ByteArray) (pa pb n i j : Nat) : ByteArray :=
  (bodyW (rowsMem mem pa pb n i) pa pb n i j).mem

def c1At (mem : ByteArray) (pa pb n i j : Nat) : UInt256 :=
  (bodyW (rowsMem mem pa pb n i) pa pb n i j).c1

def c2At (mem : ByteArray) (pa pb n i j : Nat) : UInt256 :=
  (bodyW (rowsMem mem pa pb n i) pa pb n i j).c2

def aiAt (mem : ByteArray) (pa pb n i : Nat) : UInt256 :=
  peelAi (rowsMem mem pa pb n i) pb n i

def mAt (mem : ByteArray) (pa pb n i : Nat) : UInt256 :=
  peelM (rowsMem mem pa pb n i) pa pb n i

/-- `b[j+1]`, at `p_b = p_t + dB`. -/
def bAt (mem : ByteArray) (pa pb n i j : Nat) : UInt256 :=
  MachineState.readWord (memAt mem pa pb n i j) (pa + 32 * (n - j - 2))

/-- `t[j+1]`, at `p_t`. -/
def tAt (mem : ByteArray) (pa pb n i j : Nat) : UInt256 :=
  MachineState.readWord (memAt mem pa pb n i j) (8224 + 32 * (n - j - 1))

/-- `N[j+1]`, at `p_n = p_t + dN`. -/
def nAt (mem : ByteArray) (pa pb n i j : Nat) : UInt256 :=
  MachineState.readWord (memAt mem pa pb n i j) (32 * (n - j - 2))

/-- `bodyW`'s successor case as a rewrite.  `bodyW` must never go into a simp set:
it is a recursion on `j`, and unfolding it inside `blkFiosBodyE` -- the one block whose
post-state carries index `j + 1` -- is what drives the kernel into deep recursion.  With
this lemma simp rewrites exactly once and the post-state matches. -/
theorem bodyW_succ (mem : ByteArray) (pa pb n i j : Nat) :
    bodyW mem pa pb n i (j + 1) =
      { c1 := Monpro.macCarry
                (MachineState.readWord (bodyW mem pa pb n i j).mem
                  (pa + 32 * (n - j - 2)))
                (peelAi mem pb n i)
                (MachineState.readWord (bodyW mem pa pb n i j).mem
                  (8224 + 32 * (n - j - 1)))
                (bodyW mem pa pb n i j).c1
        c2 := Monpro.macCarry
                (MachineState.readWord (bodyW mem pa pb n i j).mem
                  (32 * (n - j - 2)))
                (peelM mem pa pb n i)
                (Monpro.macSum
                  (MachineState.readWord (bodyW mem pa pb n i j).mem
                    (pa + 32 * (n - j - 2)))
                  (peelAi mem pb n i)
                  (MachineState.readWord (bodyW mem pa pb n i j).mem
                    (8224 + 32 * (n - j - 1)))
                  (bodyW mem pa pb n i j).c1)
                (bodyW mem pa pb n i j).c2
        mem := MachineState.writeBytes (bodyW mem pa pb n i j).mem
                 (Data.Bytes.natToBytesPadded
                   (Monpro.macSum
                     (MachineState.readWord (bodyW mem pa pb n i j).mem
                       (32 * (n - j - 2)))
                     (peelM mem pa pb n i)
                     (Monpro.macSum
                       (MachineState.readWord (bodyW mem pa pb n i j).mem
                         (pa + 32 * (n - j - 2)))
                       (peelAi mem pb n i)
                       (MachineState.readWord (bodyW mem pa pb n i j).mem
                         (8224 + 32 * (n - j - 1)))
                       (bodyW mem pa pb n i j).c1)
                     (bodyW mem pa pb n i j).c2).toNat 32)
                 (8256 + 32 * (n - j - 1)) } := rfl

/-- `bodyW`'s BASE case as a rewrite, for the same reason `bodyW_succ` exists.  `bodyW`
never enters a simp set, so `c1At … i 0` / `c2At … i 0` / `memAt … i 0` were opaque and
had no way to meet `peelC1` / `peelC2` / `rowsMem` on the machine side.  That is why
`blkFiosRow4`, whose post-state is `fiosBody … i 0`, failed with every `have` present. -/
theorem bodyW_zero (mem : ByteArray) (pa pb n i : Nat) :
    bodyW mem pa pb n i 0 =
      { c1 := peelC1 mem pa pb n i
        c2 := peelC2 mem pa pb n i
        mem := mem } := rfl

/-- `u`, the word after the first accumulate.  `bodyW`'s own `j+1` case is built from
exactly this, so `c1At … (j+1)` and `c2At … (j+1)` below hold by `rfl` — which is what
makes `blkFiosBodyE`'s taken arm land on `fiosBody … (j+1)` without a rewrite. -/
def uAt (mem : ByteArray) (pa pb n i j : Nat) : UInt256 :=
  Monpro.macSum (bAt mem pa pb n i j) (aiAt mem pa pb n i)
    (tAt mem pa pb n i j) (c1At mem pa pb n i j)

/-! ### The twelve block-boundary states -/

/-- pc 5351, engine entry: `blk1379` has jumped here, stack unchanged from
`Monpro.mpEntryState`. -/
def fiosEntry (s : State) (mem : ByteArray) (pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 5351
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

def fiosBody (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i j : Nat) : State :=
  { s with pc := UInt256.ofNat 5653
           stack := bodyFrame n pa pb pdst ret rest i j
             (c1At mem pa pb n i j) (c2At mem pa pb n i j)
             (mAt mem pa pb n i) (aiAt mem pa pb n i)
           memory := memAt mem pa pb n i j }

/-- pc 5705: the widening of `b[j+1] * a_i`.  Memory-pure. -/
def fiosBodyA (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i j : Nat) : State :=
  { s with pc := UInt256.ofNat 5705
           stack := Monpro.mulHi (bAt mem pa pb n i j) (aiAt mem pa pb n i)
             :: bAt mem pa pb n i j * aiAt mem pa pb n i
             :: bodyFrame n pa pb pdst ret rest i j
                  (c1At mem pa pb n i j) (c2At mem pa pb n i j)
                  (mAt mem pa pb n i) (aiAt mem pa pb n i)
           memory := memAt mem pa pb n i j }

/-- pc 5722: `u = t[j+1] + b[j+1]*a_i + C1`, carries folded into `C1'`.  Memory-pure. -/
def fiosBodyB (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i j : Nat) : State :=
  { s with pc := UInt256.ofNat 5722
           stack := uAt mem pa pb n i j
             :: UInt256.ofNat (Csub.ptrAt (8224 + 32 * n) (j + 1))
             :: c1At mem pa pb n i (j + 1)
             :: c2At mem pa pb n i j
             :: mAt mem pa pb n i :: aiAt mem pa pb n i
             :: rowFrame n pa pb pdst ret rest i
           memory := memAt mem pa pb n i j }

/-- pc 5773: the widening of `N[j+1] * m`.  Memory-pure. -/
def fiosBodyC (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i j : Nat) : State :=
  { s with pc := UInt256.ofNat 5773
           stack := Monpro.mulHi (nAt mem pa pb n i j) (mAt mem pa pb n i)
             :: nAt mem pa pb n i j * mAt mem pa pb n i
             :: uAt mem pa pb n i j
             :: UInt256.ofNat (Csub.ptrAt (8224 + 32 * n) (j + 1))
             :: c1At mem pa pb n i (j + 1)
             :: c2At mem pa pb n i j
             :: mAt mem pa pb n i :: aiAt mem pa pb n i
             :: rowFrame n pa pb pdst ret rest i
           memory := memAt mem pa pb n i j }

/-- pc 5790: `v = u + N[j+1]*m + C2`, carries folded into `C2'`.  Memory-pure; the
store is `blkFiosBodyE`'s and is the body's only write. -/
def fiosBodyD (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i j : Nat) : State :=
  { s with pc := UInt256.ofNat 5790
           stack := Monpro.macSum (nAt mem pa pb n i j) (mAt mem pa pb n i)
                      (uAt mem pa pb n i j) (c2At mem pa pb n i j)
             :: UInt256.ofNat (Csub.ptrAt (8224 + 32 * n) (j + 1))
             :: c1At mem pa pb n i (j + 1)
             :: c2At mem pa pb n i (j + 1)
             :: mAt mem pa pb n i :: aiAt mem pa pb n i
             :: rowFrame n pa pb pdst ret rest i
           memory := memAt mem pa pb n i j }


def fiosRow (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 5488
           stack := rowFrame n pa pb pdst ret rest i
           memory := rowsMem mem pa pb n i }

def fiosRowA (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 5542
           stack := Monpro.mulHi (peelB0 (rowsMem mem pa pb n i) pa n)
                      (peelAi (rowsMem mem pa pb n i) pb n i)
             :: peelB0 (rowsMem mem pa pb n i) pa n * peelAi (rowsMem mem pa pb n i) pb n i
             :: peelAi (rowsMem mem pa pb n i) pb n i
             :: rowFrame n pa pb pdst ret rest i
           memory := rowsMem mem pa pb n i }

def fiosRowB (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 5558
           stack := peelM (rowsMem mem pa pb n i) pa pb n i
             :: peelS (rowsMem mem pa pb n i) pa pb n i
             :: peelC1 (rowsMem mem pa pb n i) pa pb n i
             :: peelAi (rowsMem mem pa pb n i) pb n i
             :: rowFrame n pa pb pdst ret rest i
           memory := rowsMem mem pa pb n i }

def fiosRowC (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 5609
           stack := Monpro.mulHi (peelN0 (rowsMem mem pa pb n i) n)
                      (peelM (rowsMem mem pa pb n i) pa pb n i)
             :: peelN0 (rowsMem mem pa pb n i) n * peelM (rowsMem mem pa pb n i) pa pb n i
             :: peelM (rowsMem mem pa pb n i) pa pb n i
             :: peelS (rowsMem mem pa pb n i) pa pb n i
             :: peelC1 (rowsMem mem pa pb n i) pa pb n i
             :: peelAi (rowsMem mem pa pb n i) pb n i
             :: rowFrame n pa pb pdst ret rest i
           memory := rowsMem mem pa pb n i }

/-- pc 5838, the fused loop has fallen through with `p_t = 0x2020`. -/
def fiosTail (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { fiosBody s mem n pa pb pdst ret rest i (n - 1) with pc := UInt256.ofNat 5838 }

def fiosDone (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 5907
           stack := rowFrame n pa pb pdst ret rest n
           memory := rowsMem mem pa pb n n }


/-- pc 5866, the split point of `blkFiosTail`.  Both stores are done and the three spent
body words are popped, so the stack is EXACTLY `rowFrame … i` and the memory EXACTLY the
finished row -- no half-computed value anywhere, which is the property that makes the
intermediate state nameable without inventing anything.

The cut is chosen so that all the memory work (one `MLOAD`, two `MSTORE`s, the carry
algebra) is on one side and the whole control flow (pointer step, compare, `JUMPI`) on
the other.  The 29-instruction block needed 27 GB in a single `simp` precisely because it
is the only one that multiplies those two together. -/
def fiosTailM (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 5866
           stack := rowFrame n pa pb pdst ret rest i
           memory := rowMem (rowsMem mem pa pb n i) pa pb n i }

/-- The two sub-blocks ARE the block, by construction: `emit_fios_lean.py` decoded both
from the same bytes at indices 3139..3160 and 3161..3167.  `Located` carries proofs, but
Lean 4 has definitional proof irrelevance, so this is `rfl`. -/
theorem blkFiosTail_split : blkFiosTail = blkFiosTailA ++ blkFiosTailB := rfl

/-- pc 5829, the split point of `blkFiosBodyE`.  The store is done and `p_t` has already
stepped, so this is EXACTLY `fiosBody … i (j+1)` with a different pc -- which is the
cleanest possible intermediate state: it needs no new stack shape at all, and the
`blkFiosBodyEB` reduction becomes "the pc moves, if the branch is taken".

`blkFiosBodyE` is the body's only write AND a branch, the same shape as `blkFiosTail`,
and it failed the same way (exit 137).  Cutting after the pointer step leaves `EB` with
nothing but `PUSH2 0x2020; DUP2; GT; PUSH2 …; JUMPI` -- no memory, no arithmetic -- so
the two arms duplicate almost nothing. -/
def fiosBodyM (s : State) (mem : ByteArray) (n pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) (i j : Nat) : State :=
  { fiosBody s mem n pa pb pdst ret rest i (j + 1) with pc := UInt256.ofNat 5829 }

theorem blkFiosBodyE_split : blkFiosBodyE = blkFiosBodyEA ++ blkFiosBodyEB := rfl

/-- The accumulator pointer after the LAST body iteration, in the index form the
`n - 1 -> n - 2 + 1` normalisation leaves behind: `n - 2 + 1 + 1 = n`, so the walk
lands exactly on `&t[n] = 8224` and `blkFiosBodyE`'s `JUMPI` tests `8224 < 8224`,
which is false — the fall-through to pc 5838. -/
theorem tFallAddr_mod (n : Nat) (hn2 : 2 ≤ n) (hn32 : n ≤ 32) :
    (8224 + 32 * n + (n - 2 + 1 + 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8224 := by
  have h : n - 2 + 1 + 1 = n := by omega
  rw [h, ptrWalk_mod (8224 + 32 * n) n (by omega) (by omega)]
  omega

/-- The row pointer AFTER `ofNat_K_step` has folded the leading constant into the
index.  `bRowStep_mod` is stated with the constant still on the left, so once the
step lemma fires it can no longer match — the same normalise-then-fail trap that cost
a round on the accumulator pointer.  These two are stated in the post-step form. -/
theorem bRowStepped_mod (pb n i : Nat) (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i + 2 ≤ n) :
    (pb + 32 * n + (i + 1 + 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = pb + 32 * (n - i - 2) := by
  have h : i + 1 + 1 = i + 2 := by omega
  rw [h, ptrWalk_mod (pb + 32 * n) (i + 2) (by omega) (by omega)]
  omega

theorem bRowSteppedExit_mod (pb n : Nat) (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (_hn2 : 2 ≤ n) :
    (pb + 32 * n + (n + 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = pb - 32 := by
  rw [ptrWalk_mod (pb + 32 * n) (n + 1) (by omega) (by omega)]
  omega

/-- The row bound, `&b[0] - 32`, held in `rowFrame`'s fifth slot. -/
theorem pbBase_mod (pb n : Nat) (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192) :
    (pb + 115792089237316195423570985008687907853269984665640564039457584007913129639904) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = pb - 32 := by
  have h1 : pb + 115792089237316195423570985008687907853269984665640564039457584007913129639904 = Csub.ptrAt pb 1 := by
    simp only [Csub.ptrAt]
  rw [h1, Csub.ptrAt_mod pb 1 (by omega) (by omega)]

/-- The row pointer after row `i`'s decrement: `&b[n-i-2]`, still above the bound while
another row remains. -/
theorem bRowStep_mod (pb n i : Nat) (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i + 1 < n) :
    (115792089237316195423570985008687907853269984665640564039457584007913129639904 +
        (pb + 32 * n + (i + 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904)) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = pb + 32 * (n - i - 2) := by
  have h1 : 115792089237316195423570985008687907853269984665640564039457584007913129639904 + (pb + 32 * n + (i + 1) * 115792089237316195423570985008687907853269984665640564039457584007913129639904)
      = Csub.ptrAt (pb + 32 * n) (i + 2) := by
    simp only [Csub.ptrAt]
    omega
  rw [h1, Csub.ptrAt_mod (pb + 32 * n) (i + 2) (by omega) (by omega)]
  omega

/-- The same after the LAST row: the pointer lands exactly on the bound, `pb - 32`, so
`pb - 32 < pb - 32` is false and the row loop falls through. -/
theorem bRowExit_mod (pb n : Nat) (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192) :
    (115792089237316195423570985008687907853269984665640564039457584007913129639904 + (pb + 32 * n + n * 115792089237316195423570985008687907853269984665640564039457584007913129639904)) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936
      = pb - 32 := by
  have h1 : 115792089237316195423570985008687907853269984665640564039457584007913129639904 + (pb + 32 * n + n * 115792089237316195423570985008687907853269984665640564039457584007913129639904)
      = Csub.ptrAt (pb + 32 * n) (n + 1) := by
    simp only [Csub.ptrAt]
    omega
  rw [h1, Csub.ptrAt_mod (pb + 32 * n) (n + 1) (by omega) (by omega)]
  omega

end Challenge.Modexp.Submission.Proofs.Fast.Fios
