/-
FiosMem.lean -- the memory side of the FIOS swap.

Three things, in dependency order:

  1. `Fios.rowsMem_readWord_outside` -- the single memory obligation of the whole swap.
     Everything else about FIOS memory that anyone ever asks for goes through it.
  2. The five `Fios.monproMem_*`, each a one-line instantiation of `Monpro.monproMemOf_*`
     at `Fios.rowsMem` -- except `monproMem_represents`, which is the value law.
  3. `Fios.gasSteps_monproFull`, with `gasSteps_monproCsub`'s body shape.

ARGUMENT ORDER.  `Fios.rowMem` / `Fios.rowsMem` / `Fios.bodyW` take `(mem) (pa pb n) (i)`
here, matching `Monpro.rowsMem`, so they fit `monproMemOf`'s parameter type
`ByteArray → Nat → Nat → Nat → Nat → ByteArray` without a wrapper.  FiosRun.lean is
updated to the same order.

THE FOOTPRINT, and why the bound is comfortable:
    the fused body writes one word at   8256 + 32 * (n - j - 1),  j = 0 .. n-2
    the row tail writes                 8256   (t[n-1])  and  8224  (t[n])
    highest is 8256 + 32*(n-1) = 8224 + 32n <= 8224 + 1024 = 9248 < 9280   at n = 32
    lowest  is 8224 >= 8192
  and 8192 itself is written ONCE, by `mpZeroed`, and never again -- the CIOS rows wrote
  `t[n+1]` there on every row, the fused tail folds both carries straight into `t[n]`.
  So the FIOS footprint is a strict subset of the CIOS one and this lemma holds with the
  identical statement.
-/
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.Csub
import Challenge.Modexp.Submission.Proofs.Fast.FiosRunTop
import Challenge.Modexp.Submission.Proofs.Fast.Fios
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Fios

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

/-! ## 1.  The single memory obligation -/

/-- The fused loop writes only inside `[8192, 9280)`.  One `writeBytes … 32` per
iteration, at `8256 + 32 * (n - j - 1)`. -/
theorem readWord_bodyW (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) : ∀ j,
    MachineState.readWord (bodyW mem pa pb n i j).mem addr =
      MachineState.readWord mem addr := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      show MachineState.readWord
        (MachineState.writeBytes (bodyW mem pa pb n i j).mem
          (Data.Bytes.natToBytesPadded _ 32) (8256 + 32 * (n - j - 1))) addr = _
      rw [Monpro.readWord_storeWord_outside _ _ _ _ (by omega)]
      exact ih

/-- The row tail writes `t[n-1]` at 8256 and `t[n]` at 8224, both inside the scratch. -/
theorem readWord_rowMem (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 32) (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (rowMem mem pa pb n i) addr =
      MachineState.readWord mem addr := by
  show MachineState.readWord
    (MachineState.writeBytes
      (MachineState.writeBytes (bodyW mem pa pb n i (n - 1)).mem
        (Data.Bytes.natToBytesPadded _ 32) 8256)
      (Data.Bytes.natToBytesPadded _ 32) 8224) addr = _
  rw [Monpro.readWord_storeWord_outside _ _ _ _ (by omega),
    Monpro.readWord_storeWord_outside _ _ _ _ (by omega)]
  exact readWord_bodyW mem pa pb n i addr hn haddr (n - 1)

/-- **The obligation.**  Identical statement to `Monpro.rowsMem_readWord_outside`. -/
theorem rowsMem_readWord_outside (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 32) (hout : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (rowsMem mem pa pb n i) addr =
      MachineState.readWord mem addr := by
  induction i with
  | zero => rfl
  | succ i ih =>
      show MachineState.readWord (rowMem (rowsMem mem pa pb n i) pa pb n i) addr = _
      rw [readWord_rowMem _ pa pb n i addr hn hout]
      exact ih

/-! ## 2.  The five `monproMem_*`

`Monpro` states its own five over its own `rowsMem`, and each proof uses exactly ONE
property of the rows function: `rowsMem_readWord_outside`.  There is no `monproMemOf`
generic layer in the tree (an earlier draft of this file assumed one), so rather than
generalise `Monpro` -- 3,682 lines, and on everyone else's critical path -- these are
`Monpro`'s own proofs with `Fios.rowsMem_readWord_outside` substituted at the single
point where the row function is mentioned.  Line for line they are the CIOS proofs.

The fifth, `monproMem_represents`, is the value law and is proved from
`Fios.Arith.fios_montMul` -- the one place the arithmetic file is cashed in. -/

def monproMem (s : State) (mem : ByteArray) (pa pb n pdst : Nat) : ByteArray :=
  Csub.csResultMemory (rowsMem (Monpro.mpZeroed s mem n) pa pb n n) n pdst

theorem monproMem_def (s : State) (mem : ByteArray) (pa pb n pdst : Nat) :
    monproMem s mem pa pb n pdst =
      Csub.csResultMemory (rowsMem (Monpro.mpZeroed s mem n) pa pb n n) n pdst := rfl

theorem monproMem_readWord_outside (s : State) (mem : ByteArray)
    (pa pb n pdst addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hsubb : addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 8192 ∨ 9280 ≤ addr)
    (hdst : addr + 32 ≤ pdst ∨ pdst + 32 * n ≤ addr) :
    MachineState.readWord (monproMem s mem pa pb n pdst) addr =
      MachineState.readWord mem addr := by
  rw [monproMem_def,
    Monpro.csResultMemory_readWord_outside _ n pdst addr hn hsubb hdst,
    rowsMem_readWord_outside _ pa pb n n addr hn32 hscratch,
    Monpro.mpZeroed_readWord_outside s mem n addr (by omega)]

theorem monproMem_readWord_high (s : State) (mem : ByteArray)
    (pa pb n pdst addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hdst : pdst + 32 * n ≤ 8192) (haddr : 9280 ≤ addr) :
    MachineState.readWord (monproMem s mem pa pb n pdst) addr =
      MachineState.readWord mem addr :=
  monproMem_readWord_outside s mem pa pb n pdst addr hn hn32 (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega))

theorem monproMem_frame (s : State) (mem : ByteArray) (pa pb n pdst : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hdst : pdst + 32 * n ≤ 8192) :
    MachineState.readWord (monproMem s mem pa pb n pdst) 9344 =
        MachineState.readWord mem 9344 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9376 =
        MachineState.readWord mem 9376 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9408 =
        MachineState.readWord mem 9408 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9440 =
        MachineState.readWord mem 9440 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9472 =
        MachineState.readWord mem 9472 :=
  ⟨monproMem_readWord_high s mem pa pb n pdst 9344 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9376 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9408 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9440 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9472 hn hn32 hdst (by omega)⟩

theorem monproMem_fastRepresents_outside (s : State) (mem : ByteArray)
    (pa pb n pdst ptr cnt v : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hsubb : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 8192 ∨ 9280 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ pdst ∨ pdst + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (monproMem s mem pa pb n pdst) ptr cnt v := by
  refine (Model.fastRepresents_congr
    (a := mem) (b := monproMem s mem pa pb n pdst) ?_ v).1 hrep
  intro j hj
  exact (monproMem_readWord_outside s mem pa pb n pdst (ptr + 32 * j) hn hn32
    (by omega) (by omega) (by omega)).symm

/-! ### The value law — the bridge from bytes to the Nat families

**`Monpro.rows_invariant` is entirely generic in how a row is computed.** I read its 106
lines: the only row-specific input is `row_equation`; everything else is bookkeeping that
carries `FastRepresents` and the `minv` word across a row and then hands
`Model.cios_step` its arguments. So the FIOS version is that proof with five renamings
and ONE new obligation, `Fios.row_equation` — whose Nat core is already green as
`Fios.rowValue_mul` in FIOS_MATH.lean. -/

/-- The `(n+1)`-limb accumulator, identical to `Monpro.tValue`. -/
def tValue (mem : ByteArray) (n : Nat) : Nat :=
  (MachineState.readWord mem 8224).toNat * Limbs.radix ^ n +
    Csub.lowValue mem 8256 n n

/-- The `b` limb consumed by row `i`, identical to `Monpro.rowBi`. -/
def rowBi (mem : ByteArray) (pb n i : Nat) : UInt256 :=
  MachineState.readWord mem (pb + 32 * (n - 1 - i))

/-- The reduce multiplier row `i` chooses: the engine's `m = n0inv * S`. -/
def rowMu (mem : ByteArray) (pa pb n i : Nat) : UInt256 := peelM mem pa pb n i

theorem readWord_monpro_preserved (s : State) (memory : ByteArray)
    (pa pb n i addr : Nat) (hn : n ≤ 32)
    (haddr : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (rowsMem (Monpro.mpZeroed s memory n) pa pb n i) addr =
      MachineState.readWord memory addr := by
  rw [rowsMem_readWord_outside _ _ _ _ _ _ hn haddr,
    Monpro.readWord_mpZeroed _ _ _ _ hn haddr]

theorem fastRepresents_monpro_preserved (s : State) (memory : ByteArray)
    (pa pb n i ptr count value : Nat) (hn : n ≤ 32)
    (hfit : ptr + 32 * count ≤ 8192)
    (hrep : Model.FastRepresents memory ptr count value) :
    Model.FastRepresents (rowsMem (Monpro.mpZeroed s memory n) pa pb n i) ptr count
      value := by
  refine (Model.fastRepresents_congr
    (a := memory) (b := rowsMem (Monpro.mpZeroed s memory n) pa pb n i) ?_ value).1 hrep
  intro j hj
  rw [readWord_monpro_preserved s memory pa pb n i (ptr + 32 * j) hn (by omega)]

/-! ### 2c.  The byte-to-Nat dictionary for one row

Everything below cashes in `FIOS_MATH.lean`.  Its declarations sit in the TOP-LEVEL
namespace `Fios` (that file opens `namespace Fios` at the outermost level), while this
file is inside `Challenge.Modexp.Submission.Proofs.Fast.Fios`, so they are written
`Arith.…` throughout.

?N  RESOLVED, and the collision is REAL -- half of it was checked.  Both files are
    indeed in `…Proofs.Fast.Fios`, but it is `FiosRun.lean`, not `FiosMem`, that also
    declares `peelC1` and `peelC2` there; and `FiosMem` declares `rows_invariant`, which
    `Fios.lean` declares too.  Three names, one namespace.  Nothing importing BOTH
    modules can elaborate -- that is this file now, and `Exp.lean` at the swap.  The fix
    is one wrap: `namespace Arith` / `end Arith` around `Fios.lean`'s body, INSIDE its
    existing `namespace Fios`.  Its declarations become `Fios.Arith.…`, all three clashes
    go, and from in here `Arith.st` resolves.  This file is written that way.
?I  This file must now import the arithmetic module.  I have added
    `import Challenge.Modexp.Submission.Proofs.Fast.Fios`; correct the module name if
    you dropped it in under another one. -/

theorem radix_eq : Limbs.radix = 2 ^ 256 := rfl                                 -- ?R

/-- `t` limb `k`.  Limbs `0 .. n-1` live at `8256 + 32 * (n - 1 - k)` and limb `n` at
8224; written `8224 + 32 * (n - k)` ONE formula covers both, with no truncated
subtraction anywhere in range. -/
def rowT (mem : ByteArray) (n k : Nat) : Nat :=
  (MachineState.readWord mem (8224 + 32 * (n - k))).toNat

/-- `a` limb `k`, in the `pa` block. -/
def rowA (mem : ByteArray) (pa n k : Nat) : Nat :=
  (MachineState.readWord mem (pa + 32 * (n - 1 - k))).toNat

/-- `N` limb `k`, in the modulus block at 0. -/
def rowMm (mem : ByteArray) (n k : Nat) : Nat :=
  (MachineState.readWord mem (32 * (n - 1 - k))).toNat

theorem rowT_zero (mem : ByteArray) (n : Nat) : rowT mem n 0 = (peelT0 mem n).toNat := by
  simp only [rowT, peelT0, Nat.sub_zero]

theorem rowA_zero (mem : ByteArray) (pa n : Nat) :
    rowA mem pa n 0 = (peelB0 mem pa n).toNat := by
  simp only [rowA, peelB0, Nat.sub_zero]

theorem rowMm_zero (mem : ByteArray) (n : Nat) :
    rowMm mem n 0 = (peelN0 mem n).toNat := by
  simp only [rowMm, peelN0, Nat.sub_zero]

theorem rowT_top (mem : ByteArray) (n : Nat) :
    rowT mem n n = (MachineState.readWord mem 8224).toNat := by
  simp only [rowT, Nat.sub_self, Nat.mul_zero, Nat.add_zero]

/-! ### Three small word facts

The peel emits `t + x*y` where the body emits `c + (t + x*y)`; these three let the peel
be read as one `Monpro.macSum`/`macCarry` pair with `c = 0`, so `Monpro.macSpec` covers
it and no second copy of that 72-line proof is needed. -/

theorem gt_eq_lt (a b : UInt256) : UInt256.gt a b = UInt256.lt b a := rfl       -- ?G

theorem zero_add_word (w : UInt256) : (0 : UInt256) + w = w := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add]
  have h0 : (0 : UInt256).toNat = 0 := by decide
  rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (Monpro.word_lt_size w)]

theorem lt_zero_word (w : UInt256) : UInt256.lt w 0 = 0 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Monpro.word_toNat_lt']
  have h0 : (0 : UInt256).toNat = 0 := by decide
  rw [h0]
  simp

theorem lt_le_one (a b : UInt256) : (UInt256.lt a b).toNat ≤ 1 := by
  rw [Monpro.word_toNat_lt']
  split <;> omega

/-! ### The peel, as one `mac` step with carry-in zero -/

theorem peelS_mac (mem : ByteArray) (pa pb n i : Nat) :
    peelS mem pa pb n i
      = Monpro.macSum (peelB0 mem pa n) (peelAi mem pb n i) (peelT0 mem n) 0 := by
  simp only [peelS, Monpro.macSum]
  exact (zero_add_word _).symm

theorem peelC1_mac (mem : ByteArray) (pa pb n i : Nat) :
    peelC1 mem pa pb n i
      = Monpro.macCarry (peelB0 mem pa n) (peelAi mem pb n i) (peelT0 mem n) 0 := by
  simp only [peelC1, peelS, Monpro.macCarry]
  rw [zero_add_word, lt_zero_word, zero_add_word]

theorem peelC2_mac (mem : ByteArray) (pa pb n i : Nat) :
    peelC2 mem pa pb n i
      = Monpro.macCarry (peelN0 mem n) (peelM mem pa pb n i)
          (peelS mem pa pb n i) 0 := by
  simp only [peelC2, Monpro.macCarry, gt_eq_lt]
  rw [zero_add_word, lt_zero_word, zero_add_word]

/-- The word the peel would store below `t[0]`.  The engine never stores it; `c0_spec`
makes it zero. -/
def peelLowWord (mem : ByteArray) (pa pb n i : Nat) : UInt256 :=
  peelS mem pa pb n i + peelN0 mem n * peelM mem pa pb n i

theorem peelC1_spec (mem : ByteArray) (pa pb n i : Nat) :
    (peelC1 mem pa pb n i).toNat * 2 ^ 256 + (peelS mem pa pb n i).toNat
      = (peelT0 mem n).toNat
        + (peelB0 mem pa n).toNat * (peelAi mem pb n i).toNat := by
  have h := Monpro.macSpec (peelB0 mem pa n) (peelAi mem pb n i) (peelT0 mem n) 0
  have h0 : (0 : UInt256).toNat = 0 := by decide
  rw [peelC1_mac, peelS_mac]
  omega

theorem peelC2_spec (mem : ByteArray) (pa pb n i : Nat) :
    (peelC2 mem pa pb n i).toNat * 2 ^ 256 + (peelLowWord mem pa pb n i).toNat
      = (peelS mem pa pb n i).toNat
        + (peelN0 mem n).toNat * (peelM mem pa pb n i).toNat := by
  have h := Monpro.macSpec (peelN0 mem n) (peelM mem pa pb n i) (peelS mem pa pb n i) 0
  have hs : Monpro.macSum (peelN0 mem n) (peelM mem pa pb n i)
      (peelS mem pa pb n i) 0 = peelLowWord mem pa pb n i := by
    simp only [Monpro.macSum, peelLowWord]
    exact zero_add_word _
  rw [hs] at h
  have h0 : (0 : UInt256).toNat = 0 := by decide
  rw [peelC2_mac]
  omega

/-! ### The peel matches `Fios.peelC1` / `peelC2` / `peelLow` -/

theorem peelS_eq (mem : ByteArray) (pa pb n i : Nat) :
    (peelS mem pa pb n i).toNat
      = (rowT mem n 0 + rowA mem pa n 0 * (peelAi mem pb n i).toNat) % Limbs.radix := by
  have h := peelC1_spec mem pa pb n i
  have hlt : (peelS mem pa pb n i).toNat < 2 ^ 256 := Monpro.word_lt_size _
  rw [rowT_zero, rowA_zero, radix_eq]
  omega

theorem peelC1_eq (mem : ByteArray) (pa pb n i : Nat) :
    (peelC1 mem pa pb n i).toNat
      = Arith.peelC1 Limbs.radix (peelAi mem pb n i).toNat
          (rowT mem n) (rowA mem pa n) := by
  have h := peelC1_spec mem pa pb n i
  have hlt : (peelS mem pa pb n i).toNat < 2 ^ 256 := Monpro.word_lt_size _
  simp only [Arith.peelC1, rowT_zero, rowA_zero, radix_eq]
  omega

theorem peelC2_eq (mem : ByteArray) (pa pb n i : Nat) :
    (peelC2 mem pa pb n i).toNat
      = Arith.peelC2 Limbs.radix (peelAi mem pb n i).toNat
          (peelM mem pa pb n i).toNat (rowT mem n) (rowA mem pa n) (rowMm mem n) := by
  have h := peelC2_spec mem pa pb n i
  have hlt : (peelLowWord mem pa pb n i).toNat < 2 ^ 256 := Monpro.word_lt_size _
  have hS := peelS_eq mem pa pb n i
  rw [radix_eq] at hS
  simp only [Arith.peelC2, rowMm_zero, radix_eq]
  rw [← hS]
  omega

theorem peelLow_eq (mem : ByteArray) (pa pb n i : Nat) :
    Arith.peelLow Limbs.radix (peelAi mem pb n i).toNat
        (peelM mem pa pb n i).toNat (rowT mem n) (rowA mem pa n) (rowMm mem n)
      = (peelLowWord mem pa pb n i).toNat := by
  have h := peelC2_spec mem pa pb n i
  have hlt : (peelLowWord mem pa pb n i).toNat < 2 ^ 256 := Monpro.word_lt_size _
  have hS := peelS_eq mem pa pb n i
  rw [radix_eq] at hS
  simp only [Arith.peelLow, rowMm_zero, radix_eq]
  rw [← hS]
  omega

/-- **The peel's stored word is zero** -- `Monpro.c0_spec` transplanted.  `c0_spec`'s
`t0` is our `S` and its `minv * t0` is our `peelM`, which is literally
`readWord mem 9376 * peelS`, so it applies unchanged. -/
theorem peelLowWord_zero (mem : ByteArray) (pa pb n i : Nat)
    (hminvR : ((MachineState.readWord mem (32 * n - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    (peelLowWord mem pa pb n i).toNat = 0 := by
  have haddr : 32 * (n - 1) = 32 * n - 32 := by omega
  have hminv : ((peelN0 mem n).toNat *
      (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0 := by
    simp only [peelN0, haddr]
    exact hminvR
  have hc := Monpro.c0_spec (peelN0 mem n) (MachineState.readWord mem 9376)
    (peelS mem pa pb n i) hminv
  have hm : MachineState.readWord mem 9376 * peelS mem pa pb n i
      = peelM mem pa pb n i := rfl
  rw [hm] at hc
  have h := peelC2_spec mem pa pb n i
  have hlt : (peelLowWord mem pa pb n i).toNat < 2 ^ 256 := Monpro.word_lt_size _
  omega
/-! ### The fused loop's memory, limb by limb

`readWord_bodyW` (section 1) only says the loop leaves everything OUTSIDE `[8192,9280)`
alone.  The row equation also needs disjointness INSIDE the scratch: iteration `j'`
writes limb `j'` at `8256 + 32 * (n - j' - 1)`, so any address strictly below all of
those survives the whole loop.  That covers both operand reads the body makes -- the `t`
limb it consumes, `8224 + 32 * (n - j - 1)`, which is limb `j+1`, one below limb `j`
that the same iteration stores -- and the top limb at 8224. -/
theorem readWord_bodyW_below (mem : ByteArray) (pa pb n i addr : Nat) : ∀ j,
    (∀ j', j' < j → addr + 32 ≤ 8256 + 32 * (n - j' - 1)) →
      MachineState.readWord (bodyW mem pa pb n i j).mem addr =
        MachineState.readWord mem addr := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro h
      have hd := h j (by omega)
      show MachineState.readWord
        (MachineState.writeBytes (bodyW mem pa pb n i j).mem
          (Data.Bytes.natToBytesPadded _ 32) (8256 + 32 * (n - j - 1))) addr = _
      rw [Monpro.readWord_storeWord_outside _ _ _ _ (by omega)]
      exact ih (fun j' hj' => h j' (by omega))

/-! ### One multiply-accumulate step in `Fios.st`'s `divMod` form

This is the ONLY place the byte model and the Nat model meet, and it is three lines:
`Monpro.macSpec` says `carry * β + sum = t + x*y + c` and `sum < β`, which pins `carry`
and `sum` to the quotient and remainder.  `Fios.st` is written with exactly those. -/
theorem mac_step (x y t c : UInt256) :
    (Monpro.macCarry x y t c).toNat
        = (t.toNat + x.toNat * y.toNat + c.toNat) / Limbs.radix
  ∧ (Monpro.macSum x y t c).toNat
        = (t.toNat + x.toNat * y.toNat + c.toNat) % Limbs.radix := by
  have h := Monpro.macSpec x y t c
  have hlt : (Monpro.macSum x y t c).toNat < 2 ^ 256 := Monpro.word_lt_size _
  rw [radix_eq]
  omega

/-- The Nat-model state row `i` of `mem` tracks. -/
def rowSt (mem : ByteArray) (pa pb n i : Nat) : Nat → Nat × Nat × Nat :=
  Arith.st Limbs.radix (peelAi mem pb n i).toNat (peelM mem pa pb n i).toNat
    (rowT mem n) (rowA mem pa n) (rowMm mem n)
    (peelC1 mem pa pb n i).toNat (peelC2 mem pa pb n i).toNat

/-- `rowSt` seeded from the BYTE peel is the same family `Fios.rowValue` is built from,
which is seeded from the NAT peel. -/
theorem rowSt_eq (mem : ByteArray) (pa pb n i k : Nat) :
    rowSt mem pa pb n i k
      = Arith.st Limbs.radix (peelAi mem pb n i).toNat
          (peelM mem pa pb n i).toNat (rowT mem n) (rowA mem pa n) (rowMm mem n)
          (Arith.peelC1 Limbs.radix (peelAi mem pb n i).toNat
            (rowT mem n) (rowA mem pa n))
          (Arith.peelC2 Limbs.radix (peelAi mem pb n i).toNat
            (peelM mem pa pb n i).toNat (rowT mem n) (rowA mem pa n) (rowMm mem n))
          k := by
  simp only [rowSt, peelC1_eq, peelC2_eq]

/-- **The fused loop computes `Fios.st`.**

?F  This REPLACES the `fused_invariant` that stood here, and I have to report that the
    statement I left was WRONG, not merely unproved.  It equated the loop's stored limbs
    with `limbSum` of the ORIGINAL `t` limbs and carried no `a_i · b` or `mu · m` term at
    all, where `Fios.st_invariant`'s right-hand side is `rowSum`, which carries both.
    It is false for every row that multiplies anything, so no amount of work on it would
    have closed.  Proving the CORRESPONDENCE instead is also strictly better: it lets
    `Fios.st_invariant`, `Fios.rowValue_mul` and `Fios.fios_row_eq` be used exactly as
    they are, and nothing involving `β ^ j` has to be redone at the byte level -- the
    only arithmetic here is `divMod` with a literal modulus, which `omega` closes.

The three components are the loop's two carries and the value of the limbs it has
stored.  Iteration `j+1` reads `t`, `a` and `N` at limb index `j+1` and stores at digit
position `j`, which is precisely `Fios.st`'s successor case. -/
theorem bodyW_st (mem : ByteArray) (pa pb n i : Nat)
    (hn32 : n ≤ 32) (hpaFit : pa + 32 * n ≤ 8192) : ∀ j, j + 1 ≤ n →
    (bodyW mem pa pb n i j).c1.toNat = (rowSt mem pa pb n i j).2.1
  ∧ (bodyW mem pa pb n i j).c2.toNat = (rowSt mem pa pb n i j).2.2
  ∧ Monpro.limbSum (fun k => (MachineState.readWord (bodyW mem pa pb n i j).mem
        (8256 + 32 * (n - 1 - k))).toNat) j = (rowSt mem pa pb n i j).1 := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨?_, ?_, ?_⟩
      · simp only [bodyW_zero, rowSt, Arith.st_zero]
      · simp only [bodyW_zero, rowSt, Arith.st_zero]
      · simp only [rowSt, Arith.st_zero, Monpro.limbSum_zero]
  | succ j ih =>
      intro hj
      obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
      simp only [rowSt] at ih1 ih2 ih3
      -- the three operand reads, resolved back to `mem`
      have hTr : MachineState.readWord (bodyW mem pa pb n i j).mem
            (8224 + 32 * (n - j - 1))
          = MachineState.readWord mem (8224 + 32 * (n - j - 1)) := by
        refine readWord_bodyW_below mem pa pb n i _ j ?_
        intro j' hj'
        omega
      have hAr : MachineState.readWord (bodyW mem pa pb n i j).mem
            (pa + 32 * (n - j - 2))
          = MachineState.readWord mem (pa + 32 * (n - j - 2)) :=
        readWord_bodyW mem pa pb n i _ hn32 (Or.inl (by omega)) j
      have hMr : MachineState.readWord (bodyW mem pa pb n i j).mem (32 * (n - j - 2))
          = MachineState.readWord mem (32 * (n - j - 2)) :=
        readWord_bodyW mem pa pb n i _ hn32 (Or.inl (by omega)) j
      have eT : n - (j + 1) = n - j - 1 := by omega
      have eA : n - 1 - (j + 1) = n - j - 2 := by omega
      have hT : rowT mem n (j + 1)
          = (MachineState.readWord (bodyW mem pa pb n i j).mem
              (8224 + 32 * (n - j - 1))).toNat := by
        rw [hTr]; simp only [rowT, eT]
      have hA : rowA mem pa n (j + 1)
          = (MachineState.readWord (bodyW mem pa pb n i j).mem
              (pa + 32 * (n - j - 2))).toNat := by
        rw [hAr]; simp only [rowA, eA]
      have hM : rowMm mem n (j + 1)
          = (MachineState.readWord (bodyW mem pa pb n i j).mem
              (32 * (n - j - 2))).toNat := by
        rw [hMr]; simp only [rowMm, eA]
      -- the two multiply-accumulate steps
      obtain ⟨hc1', hu'⟩ := mac_step
        (MachineState.readWord (bodyW mem pa pb n i j).mem (pa + 32 * (n - j - 2)))
        (peelAi mem pb n i)
        (MachineState.readWord (bodyW mem pa pb n i j).mem (8224 + 32 * (n - j - 1)))
        (bodyW mem pa pb n i j).c1
      obtain ⟨hc2', hv'⟩ := mac_step
        (MachineState.readWord (bodyW mem pa pb n i j).mem (32 * (n - j - 2)))
        (peelM mem pa pb n i)
        (Monpro.macSum
          (MachineState.readWord (bodyW mem pa pb n i j).mem (pa + 32 * (n - j - 2)))
          (peelAi mem pb n i)
          (MachineState.readWord (bodyW mem pa pb n i j).mem
            (8224 + 32 * (n - j - 1)))
          (bodyW mem pa pb n i j).c1)
        (bodyW mem pa pb n i j).c2
      refine ⟨?_, ?_, ?_⟩
      · rw [bodyW_succ]
        simp only [rowSt, Arith.st]
        rw [hT, hA, ← ih1]
        exact hc1'
      · rw [bodyW_succ]
        simp only [rowSt, Arith.st]
        rw [hT, hA, hM, ← ih1, ← ih2, hc2', hu']
      · rw [Monpro.limbSum_succ]
        have hcong : Monpro.limbSum (fun k => (MachineState.readWord
              (bodyW mem pa pb n i (j + 1)).mem (8256 + 32 * (n - 1 - k))).toNat) j
            = Monpro.limbSum (fun k => (MachineState.readWord
              (bodyW mem pa pb n i j).mem (8256 + 32 * (n - 1 - k))).toNat) j := by
          refine Monpro.limbSum_congr j ?_
          intro k hk
          have hw : MachineState.readWord (bodyW mem pa pb n i (j + 1)).mem
                (8256 + 32 * (n - 1 - k))
              = MachineState.readWord (bodyW mem pa pb n i j).mem
                (8256 + 32 * (n - 1 - k)) := by
            rw [bodyW_succ]
            exact Monpro.readWord_storeWord_outside _ _ _ _ (by omega)
          rw [hw]
        have hstore : (MachineState.readWord (bodyW mem pa pb n i (j + 1)).mem
              (8256 + 32 * (n - 1 - j))).toNat
            = (Monpro.macSum
                (MachineState.readWord (bodyW mem pa pb n i j).mem (32 * (n - j - 2)))
                (peelM mem pa pb n i)
                (Monpro.macSum
                  (MachineState.readWord (bodyW mem pa pb n i j).mem
                    (pa + 32 * (n - j - 2)))
                  (peelAi mem pb n i)
                  (MachineState.readWord (bodyW mem pa pb n i j).mem
                    (8224 + 32 * (n - j - 1)))
                  (bodyW mem pa pb n i j).c1)
                (bodyW mem pa pb n i j).c2).toNat := by
          have hjj : n - 1 - j = n - j - 1 := by omega
          rw [hjj, bodyW_succ]
          exact congrArg _ (Challenge.EvmProof.Memory.readWord_writeWord _ _ _)
        rw [hcong, ih3, hstore]
        simp only [rowSt, Arith.st]
        rw [hv', hu', hT, hA, hM, ← ih1, ← ih2]
/-! ### The row tail

`Fios.rowValue`'s last two summands are the tail: the word stored at `t[n-1]` and the
carry word left at `t[n]`.  The engine computes them as `x1 = t[n] + C1`, `x2 = x1 + C2`
and the two carry-out flags, which is `Monpro.add_carry_split` twice -- exactly as CIOS's
top limb, unchanged by the patch.  Naming the three words here also isolates the one
address quirk in `Fios.rowMem`: it reads `t[n]` as `8224 + 32 * n - 32 * n`. -/

def tailX1 (mem : ByteArray) (pa pb n i : Nat) : UInt256 :=
  MachineState.readWord (bodyW mem pa pb n i (n - 1)).mem 8224
    + (bodyW mem pa pb n i (n - 1)).c1

def tailX2 (mem : ByteArray) (pa pb n i : Nat) : UInt256 :=
  tailX1 mem pa pb n i + (bodyW mem pa pb n i (n - 1)).c2

def tailTn (mem : ByteArray) (pa pb n i : Nat) : UInt256 :=
  UInt256.lt (tailX1 mem pa pb n i) (bodyW mem pa pb n i (n - 1)).c1
    + UInt256.gt (bodyW mem pa pb n i (n - 1)).c2 (tailX2 mem pa pb n i)

theorem rowMem_def (mem : ByteArray) (pa pb n i : Nat) :
    rowMem mem pa pb n i
      = MachineState.writeBytes
          (MachineState.writeBytes (bodyW mem pa pb n i (n - 1)).mem
            (Data.Bytes.natToBytesPadded (tailX2 mem pa pb n i).toNat 32) 8256)
          (Data.Bytes.natToBytesPadded (tailTn mem pa pb n i).toNat 32) 8224 := by
  have h : 8224 + 32 * n - 32 * n = 8224 := by omega
  simp only [rowMem, tailX1, tailX2, tailTn, h]

theorem readWord_rowMem_ts (mem : ByteArray) (pa pb n i : Nat) :
    MachineState.readWord (rowMem mem pa pb n i) 8256 = tailX2 mem pa pb n i := by
  rw [rowMem_def, Monpro.readWord_storeWord_outside _ _ _ _ (by omega)]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem readWord_rowMem_tn (mem : ByteArray) (pa pb n i : Nat) :
    MachineState.readWord (rowMem mem pa pb n i) 8224 = tailTn mem pa pb n i := by
  rw [rowMem_def]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem readWord_rowMem_low (mem : ByteArray) (pa pb n i k : Nat) (hk : k + 1 < n) :
    MachineState.readWord (rowMem mem pa pb n i) (8256 + 32 * (n - 1 - k))
      = MachineState.readWord (bodyW mem pa pb n i (n - 1)).mem
          (8256 + 32 * (n - 1 - k)) := by
  rw [rowMem_def, Monpro.readWord_storeWord_outside _ _ _ _ (by omega),
    Monpro.readWord_storeWord_outside _ _ _ _ (by omega)]

/-- `t[n]` survives the whole fused loop: every write is at `8256` or above. -/
theorem readWord_bodyW_tn (mem : ByteArray) (pa pb n i j : Nat) :
    MachineState.readWord (bodyW mem pa pb n i j).mem 8224
      = MachineState.readWord mem 8224 :=
  readWord_bodyW_below mem pa pb n i 8224 j (fun _ _ => by omega)

theorem tailX1_toNat (mem : ByteArray) (pa pb n i : Nat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32) (hpaFit : pa + 32 * n ≤ 8192) :
    (tailX1 mem pa pb n i).toNat
      = (rowT mem n n + (rowSt mem pa pb n i (n - 1)).2.1) % Limbs.radix := by
  obtain ⟨h1, _, _⟩ := bodyW_st mem pa pb n i hn32 hpaFit (n - 1) (by omega)
  simp only [tailX1, Challenge.EvmProof.Word.word_toNat_add]
  rw [readWord_bodyW_tn, ← rowT_top, h1, radix_eq]

theorem tailX2_toNat (mem : ByteArray) (pa pb n i : Nat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32) (hpaFit : pa + 32 * n ≤ 8192) :
    (tailX2 mem pa pb n i).toNat
      = ((rowT mem n n + (rowSt mem pa pb n i (n - 1)).2.1) % Limbs.radix
          + (rowSt mem pa pb n i (n - 1)).2.2) % Limbs.radix := by
  obtain ⟨_, h2, _⟩ := bodyW_st mem pa pb n i hn32 hpaFit (n - 1) (by omega)
  simp only [tailX2, Challenge.EvmProof.Word.word_toNat_add]
  rw [tailX1_toNat mem pa pb n i hn2 hn32 hpaFit, h2, radix_eq]

theorem tailTn_toNat (mem : ByteArray) (pa pb n i : Nat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32) (hpaFit : pa + 32 * n ≤ 8192) :
    (tailTn mem pa pb n i).toNat
      = (rowT mem n n + (rowSt mem pa pb n i (n - 1)).2.1) / Limbs.radix
        + ((rowT mem n n + (rowSt mem pa pb n i (n - 1)).2.1) % Limbs.radix
            + (rowSt mem pa pb n i (n - 1)).2.2) / Limbs.radix := by
  obtain ⟨h1, h2, _⟩ := bodyW_st mem pa pb n i hn32 hpaFit (n - 1) (by omega)
  have e1 : tailX1 mem pa pb n i
      = MachineState.readWord (bodyW mem pa pb n i (n - 1)).mem 8224
        + (bodyW mem pa pb n i (n - 1)).c1 := rfl
  have e2 : tailX2 mem pa pb n i
      = tailX1 mem pa pb n i + (bodyW mem pa pb n i (n - 1)).c2 := rfl
  have ha1 := Monpro.add_carry_split
    (MachineState.readWord (bodyW mem pa pb n i (n - 1)).mem 8224)
    (bodyW mem pa pb n i (n - 1)).c1
  have ha2 := Monpro.add_carry_split (tailX1 mem pa pb n i)
    (bodyW mem pa pb n i (n - 1)).c2
  rw [← e1] at ha1
  rw [← e2] at ha2
  have hb1 : (UInt256.lt (tailX1 mem pa pb n i)
      (bodyW mem pa pb n i (n - 1)).c1).toNat ≤ 1 := lt_le_one _ _
  have hb2 : (UInt256.lt (tailX2 mem pa pb n i)
      (bodyW mem pa pb n i (n - 1)).c2).toNat ≤ 1 := lt_le_one _ _
  have hx1 : (tailX1 mem pa pb n i).toNat < 2 ^ 256 := Monpro.word_lt_size _
  have hx2 : (tailX2 mem pa pb n i).toNat < 2 ^ 256 := Monpro.word_lt_size _
  have hsum : (tailTn mem pa pb n i).toNat
      = (UInt256.lt (tailX1 mem pa pb n i) (bodyW mem pa pb n i (n - 1)).c1).toNat
        + (UInt256.lt (tailX2 mem pa pb n i)
            (bodyW mem pa pb n i (n - 1)).c2).toNat := by
    simp only [tailTn, gt_eq_lt, Challenge.EvmProof.Word.word_toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  have hT8224 : (MachineState.readWord (bodyW mem pa pb n i (n - 1)).mem 8224).toNat
      = rowT mem n n := by rw [readWord_bodyW_tn, rowT_top]
  rw [hsum, radix_eq]
  rw [hT8224, h1] at ha1
  rw [h2] at ha2
  rw [tailX1_toNat mem pa pb n i hn2 hn32 hpaFit, radix_eq] at ha2
  omega

/-! ### `limbSum` at the two radices, and the top limb -/

theorem limbSum_radix (f : Nat → Nat) : ∀ k,
    Arith.limbSum Limbs.radix f k = Monpro.limbSum f k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      show Arith.limbSum Limbs.radix f k + f k * Limbs.radix ^ k
        = Monpro.limbSum f k + f k * Limbs.radix ^ k
      rw [ih]

theorem limbSum_top (f : Nat → Nat) (n : Nat) (hn1 : 1 ≤ n) :
    Monpro.limbSum f n
      = Monpro.limbSum f (n - 1) + f (n - 1) * Limbs.radix ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact Monpro.limbSum_succ f m

/-- **The row's accumulator is `Fios.rowValue`.**  This is the byte-level half of the
row equation, and the only genuinely new content in the layer: the loop's stored limbs
are `st.1` (that is `bodyW_st`), the word at `t[n-1]` is the tail's `x2`, and the word
at `t[n]` is the tail's two carry flags. -/
theorem tValue_rowMem (mem : ByteArray) (pa pb n i : Nat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32) (hpaFit : pa + 32 * n ≤ 8192) :
    tValue (rowMem mem pa pb n i) n
      = Arith.rowValue Limbs.radix (peelAi mem pb n i).toNat
          (peelM mem pa pb n i).toNat (rowT mem n) (rowA mem pa n) (rowMm mem n)
          (n - 1) := by
  obtain ⟨_, _, h3⟩ := bodyW_st mem pa pb n i hn32 hpaFit (n - 1) (by omega)
  have hlow : Csub.lowValue (rowMem mem pa pb n i) 8256 n n
      = (rowSt mem pa pb n i (n - 1)).1
        + (tailX2 mem pa pb n i).toNat * Limbs.radix ^ (n - 1) := by
    rw [← Monpro.limbSum_eq_lowValue, limbSum_top _ n (by omega)]
    have hcong : Monpro.limbSum (fun k => (MachineState.readWord
          (rowMem mem pa pb n i) (8256 + 32 * (n - 1 - k))).toNat) (n - 1)
        = Monpro.limbSum (fun k => (MachineState.readWord
          (bodyW mem pa pb n i (n - 1)).mem (8256 + 32 * (n - 1 - k))).toNat) (n - 1) := by
      refine Monpro.limbSum_congr (n - 1) ?_
      intro k hk
      exact congrArg _ (readWord_rowMem_low mem pa pb n i k (by omega))
    have hlast : (MachineState.readWord (rowMem mem pa pb n i)
          (8256 + 32 * (n - 1 - (n - 1)))).toNat = (tailX2 mem pa pb n i).toNat := by
      have h0 : 8256 + 32 * (n - 1 - (n - 1)) = 8256 := by omega
      rw [h0, readWord_rowMem_ts]
    rw [hcong, h3, hlast]
  have hk1 : n - 1 + 1 = n := by omega
  have hpow : Limbs.radix ^ (n - 1 + 1) = Limbs.radix ^ n := by rw [hk1]
  simp only [tValue, Arith.rowValue]
  rw [hlow, readWord_rowMem_tn, tailTn_toNat mem pa pb n i hn2 hn32 hpaFit,
    tailX2_toNat mem pa pb n i hn2 hn32 hpaFit, hpow, hk1, rowSt_eq]
  omega                                                                        -- ?T

/-! ### The two limb sums the outer loop hands in -/

theorem limbSum_rowA (mem : ByteArray) (pa n a : Nat)
    (hpaR : Model.FastRepresents mem pa n a) :
    Arith.limbSum Limbs.radix (rowA mem pa n) n = a := by
  rw [limbSum_radix]
  exact Monpro.limbSum_fastRepresents hpaR

theorem limbSum_rowMm (mem : ByteArray) (n mm : Nat)
    (hmR : Model.FastRepresents mem 0 n mm) :
    Arith.limbSum Limbs.radix (rowMm mem n) n = mm := by
  rw [limbSum_radix]
  have h := Monpro.limbSum_fastRepresents hmR
  simp only [Nat.zero_add] at h
  exact h

theorem limbSum_rowT (mem : ByteArray) (n : Nat) (_hn2 : 2 ≤ n) :
    Arith.limbSum Limbs.radix (rowT mem n) (n + 1) = tValue mem n := by
  rw [limbSum_radix, Monpro.limbSum_succ]
  have hcong : Monpro.limbSum (rowT mem n) n
      = Monpro.limbSum (fun k => (MachineState.readWord mem
          (8256 + 32 * (n - 1 - k))).toNat) n := by
    refine Monpro.limbSum_congr n ?_
    intro k hk
    have haddr : 8224 + 32 * (n - k) = 8256 + 32 * (n - 1 - k) := by omega
    simp only [rowT, haddr]
  rw [hcong, Monpro.limbSum_eq_lowValue, rowT_top]
  simp only [tValue]
  omega

/-- **One FIOS row is exact.** The mirror of `Monpro.row_equation`.

It is SHORTER than the CIOS original, and here is where each of its seven facts went.
`Monpro.row_equation` assembles

    hA, hB   two top-limb carry splits              (`add_carry_split`)
    hC       the peel's divisibility                (`c0_spec`)
    hD       the L2 (reduce) loop invariant         (`l2_invariant`)
    hE, hF   limb-sum bookkeeping                   (`limbSum_shift/_congr/_fastRepresents`)
    hG       the L1 (multiply) row identity         (`l1_row`)

and hands them to `row_alg`.  FIOS collapses that:

  * `hD` and `hG` become the ONE correspondence `bodyW_st` -- there is one fused loop,
    not two -- after which `Fios.st_invariant` does the work, already green.
  * `hC` is `peelLowWord_zero` above, which is `Monpro.c0_spec` transplanted unchanged.
  * `row_alg` is not needed at all.  FIOS's pure algebra is `Fios.rowValue_mul`, proved
    in the arithmetic file; `Fios.fios_row_eq` is it in the outer loop's own shape.
  * `hA`/`hB` survive as `tailTn_toNat`: the fused tail computes `x1 = t[n] + C1` then
    `x2 = x1 + C2`, which is `add_carry_split` twice, exactly as CIOS's top limb is.
  * `hE`/`hF` survive as the three `limbSum_row*` lemmas: the accumulator layout is
    unchanged by the patch, so this is the CIOS bookkeeping verbatim.

?H  I had to ADD `hn2 : 2 ≤ n`.  The statement as it stood was not provable without it
    (`n - 1` is truncated at `n = 0`, and the tail reads `t[n]` at `8224`), and every
    call site already has it: `rows_invariant` instantiates `n := p + 2`.  I have
    updated the one call site below to pass `(by omega)`. -/
theorem row_equation (mem : ByteArray) (pa pb n i : Nat) (a mm tlow : Nat)
    (hn32 : n ≤ 32) (hn2 : 2 ≤ n) (hpaFit : pa + 32 * n ≤ 8192)
    (hpaR : Model.FastRepresents mem pa n a)
    (hmR : Model.FastRepresents mem 0 n mm)
    (_hlow : Model.FastRepresents mem 8256 n tlow)
    (hminvR : ((MachineState.readWord mem (32 * n - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    tValue (rowMem mem pa pb n i) n * Limbs.radix =
      tValue mem n + a * (rowBi mem pb n i).toNat +
        (rowMu mem pa pb n i).toNat * mm := by
  have hpeel0 : Arith.peelLow Limbs.radix (peelAi mem pb n i).toNat
      (peelM mem pa pb n i).toNat (rowT mem n) (rowA mem pa n) (rowMm mem n) = 0 := by
    rw [peelLow_eq]
    exact peelLowWord_zero mem pa pb n i hminvR
  have hrow := Arith.fios_row_eq Limbs.radix (peelAi mem pb n i).toNat
    (peelM mem pa pb n i).toNat (rowT mem n) (rowA mem pa n) (rowMm mem n) (n - 1) hpeel0
  have hk1 : n - 1 + 1 = n := by omega
  have hk2 : n - 1 + 2 = n + 1 := by omega
  rw [hk1, hk2, limbSum_rowT mem n hn2, limbSum_rowA mem pa n a hpaR,
    limbSum_rowMm mem n mm hmR] at hrow
  have hbi : (rowBi mem pb n i).toNat = (peelAi mem pb n i).toNat := rfl
  have hmu : (rowMu mem pa pb n i).toNat = (peelM mem pa pb n i).toNat := rfl
  rw [tValue_rowMem mem pa pb n i hn2 hn32 hpaFit, hbi, hmu, hrow]

/-- **The outer invariant.** `Monpro.rows_invariant`'s proof, verbatim, with
`Monpro.rowsMem → Fios.rowsMem`, `Monpro.rowMem → Fios.rowMem`,
`Monpro.rowMu (rowL1 …) → Fios.rowMu`, `Monpro.row_equation → Fios.row_equation`, and
the two `*_monpro_preserved` lemmas above. Nothing else moves — the induction, the
`Model.cios_step` application and the `Q + mu * radix ^ i` witness are unchanged, because
CIOS and FIOS compute the SAME row function. That is the whole point of the patch, and
this proof is where it pays. -/
theorem rows_invariant (s : State) (mem : ByteArray) (pa pb p : Nat) (a b mm : Nat)
    (hn32 : p + 2 ≤ 32)
    (hpaFit : pa + 32 * (p + 2) ≤ 8192) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    ∀ i, i ≤ p + 2 → ∃ Q,
      tValue (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) (p + 2) *
          Limbs.radix ^ i = a * (b % Limbs.radix ^ i) + Q * mm ∧
        tValue (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) (p + 2)
          < 2 * mm := by
  intro i
  induction i with
  | zero =>
      intro _
      have hlow0 : Csub.lowValue (Monpro.mpZeroed s mem (p + 2)) 8256 (p + 2) (p + 2)
          = 0 :=
        Model.fastRepresents_value_unique
          (Csub.fastRepresents_lowValue (Monpro.mpZeroed s mem (p + 2)) 8256 (p + 2))
          (Monpro.fastRepresents_mpZeroed s mem (p + 2))
      have hzero : tValue (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) 0)
          (p + 2) = 0 := by
        show tValue (Monpro.mpZeroed s mem (p + 2)) (p + 2) = 0
        simp only [tValue, hlow0, Monpro.readWord_mpZeroed_tn,
          Challenge.EvmProof.Word.word_toNat_ofNat]
        simp
      exact ⟨0, by rw [hzero, pow_zero, Nat.mod_one]; simp, by rw [hzero]; omega⟩
  | succ i ih =>
      intro hi
      obtain ⟨Q, hinv, hlt⟩ := ih (by omega)
      simp only [tValue] at hinv hlt ⊢
      simp only [rowsMem]
      have hpaR : Model.FastRepresents
          (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) pa (p + 2) a :=
        fastRepresents_monpro_preserved s mem pa pb (p + 2) i pa (p + 2) a hn32 hpaFit ha
      have hpbR : Model.FastRepresents
          (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) pb (p + 2) b :=
        fastRepresents_monpro_preserved s mem pa pb (p + 2) i pb (p + 2) b hn32 hpbFit hb
      have hmR : Model.FastRepresents
          (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) 0 (p + 2) mm :=
        fastRepresents_monpro_preserved s mem pa pb (p + 2) i 0 (p + 2) mm hn32
          (by omega) hm
      have hminvR : ((MachineState.readWord
            (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
            (32 * (p + 2) - 32)).toNat *
          (MachineState.readWord
            (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) 9376).toNat + 1) %
          2 ^ 256 = 0 := by
        rw [readWord_monpro_preserved s mem pa pb (p + 2) i (32 * (p + 2) - 32) hn32
            (Or.inl (by omega)),
          readWord_monpro_preserved s mem pa pb (p + 2) i 9376 hn32 (Or.inr (by omega))]
        exact hminv
      have hrow := row_equation (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
        pa pb (p + 2) i a mm
        (Csub.lowValue (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) 8256
          (p + 2) (p + 2))
        hn32 (by omega) hpaFit hpaR hmR
        (Csub.fastRepresents_lowValue
          (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) 8256 (p + 2))
        hminvR
      have hbi : (rowBi (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pb (p + 2) i).toNat = b / Limbs.radix ^ i % Limbs.radix := by
        simp only [rowBi]
        exact Model.readLimb_of_fastRepresents hpbR (by omega)
      simp only [tValue] at hrow
      have hdiv : Limbs.radix ∣
          (MachineState.readWord
              (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              8224).toNat * Limbs.radix ^ (p + 2) +
            Csub.lowValue (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) 8256
              (p + 2) (p + 2) +
            a * (rowBi (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pb (p + 2) i).toNat +
            (rowMu (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pa pb (p + 2) i).toNat * mm := by
        refine ⟨(MachineState.readWord
              (rowMem (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
                pa pb (p + 2) i) 8224).toNat * Limbs.radix ^ (p + 2) +
            Csub.lowValue
              (rowMem (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
                pa pb (p + 2) i) 8256 (p + 2) (p + 2), ?_⟩
        rw [← hrow]
        ring
      -- `Monpro.div_of_mul` is `private`; inlined here rather than widening its
      -- visibility surface (two lines, per the coordinator's instruction).
      have hquot :
          ((MachineState.readWord
              (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) 8224).toNat *
              Limbs.radix ^ (p + 2) +
            Csub.lowValue (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              8256 (p + 2) (p + 2) +
            a * (rowBi (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pb (p + 2) i).toNat +
            (rowMu (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pa pb (p + 2) i).toNat * mm) / Limbs.radix =
          (MachineState.readWord
              (rowMem (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
                pa pb (p + 2) i) 8224).toNat * Limbs.radix ^ (p + 2) +
            Csub.lowValue
              (rowMem (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
                pa pb (p + 2) i) 8256 (p + 2) (p + 2) := by
        rw [← hrow, Nat.mul_div_assoc _ (dvd_refl Limbs.radix),
          Nat.div_self Limbs.radix_pos, Nat.mul_one]
      obtain ⟨hstep1, hstep2⟩ := Model.cios_step (β := Limbs.radix) (m := mm) (a := a)
        (bpre := b % Limbs.radix ^ i)
        (bi := (rowBi (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pb (p + 2) i).toNat)
        (t := (MachineState.readWord
            (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) 8224).toNat *
            Limbs.radix ^ (p + 2) +
          Csub.lowValue (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i) 8256
            (p + 2) (p + 2))
        (Q := Q)
        (mu := (rowMu (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pa pb (p + 2) i).toNat) (i := i)
        Limbs.radix_pos ham (Monpro.word_lt_size _) hlt (Monpro.word_lt_size _) hinv hdiv
      refine ⟨Q + (rowMu (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) i)
        pa pb (p + 2) i).toNat * Limbs.radix ^ i, ?_, ?_⟩
      · rw [← hquot, hstep1, Monpro.mod_pow_succ, hbi]
      · rw [← hquot]
        exact hstep2

/-- `t[n] ≤ 1`, closing `?C`: `Fios.top_limb_le_one` from FIOS_MATH.lean applied to the
invariant at `i = p + 2`, exactly as `Monpro.monpro_tn_le_one` does. -/
theorem tn_le_one (s : State) (mem : ByteArray) (pa pb p : Nat) (a b mm : Nat)
    (hn32 : p + 2 ≤ 32)
    (hpaFit : pa + 32 * (p + 2) ≤ 8192) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    (MachineState.readWord
        (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 8224).toNat
      ≤ 1 := by
  obtain ⟨Q, -, hlt⟩ := rows_invariant s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb hm
    ham hmpos hminv (p + 2) (Nat.le_refl _)
  simp only [tValue] at hlt
  exact Arith.top_limb_le_one (β := Limbs.radix) (n := p + 2) hm.1 hlt                 -- ?E

/-- The FIOS value law: `MONPRO` followed by `CSUB` writes the Montgomery product.
`Monpro.monpro_represents`'s proof with `rows_invariant` and `tn_le_one` swapped in. -/
theorem monpro_represents (s : State) (mem : ByteArray) (pa pb p pdst : Nat)
    (a b mm : Nat) (hn32 : p + 2 ≤ 32)
    (hpaFit : pa + 32 * (p + 2) ≤ 8192) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents
      (Csub.csResultMemory
        (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) (p + 2) pdst)
      pdst (p + 2) (Model.montMul mm (Limbs.radix ^ (p + 2)) a b) := by
  have hmpos : 0 < mm := by omega
  obtain ⟨Q, hinv, hlt⟩ := rows_invariant s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb
    hm ham hmpos hminv (p + 2) (Nat.le_refl _)
  have htn1 := tn_le_one s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb hm ham hmpos hminv
  have hbmod : b % Limbs.radix ^ (p + 2) = b := Nat.mod_eq_of_lt hb.1
  rw [hbmod] at hinv
  have hcop : Nat.Coprime (Limbs.radix ^ (p + 2)) mm :=
    Model.coprime_radix_pow_of_odd hodd (p + 2)
  have hval : Model.montMul mm (Limbs.radix ^ (p + 2)) a b =
      tValue (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) (p + 2)
        % mm :=
    Model.montMul_eq_mod_of_mul_eq hmpos hcop hinv
  have hmR : Model.FastRepresents
      (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 0 (p + 2) mm :=
    fastRepresents_monpro_preserved s mem pa pb (p + 2) (p + 2) 0 (p + 2) mm hn32
      (by omega) hm
  rw [hval]
  simp only [tValue] at hlt ⊢
  exact Csub.csub_correct
    (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) (p + 2)
    (Csub.lowValue (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 8256
      (p + 2) (p + 2))
    mm
    (MachineState.readWord
      (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 8224).toNat
    pdst (by omega) hn32
    (Csub.fastRepresents_lowValue
      (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 8256 (p + 2))
    hmR rfl htn1 hmpos hlt

theorem monproMem_represents (s : State) (mem : ByteArray) (pa pb p pdst : Nat)
    (a b mm : Nat) (hn32 : p + 2 ≤ 32)
    (hpaFit : pa + 32 * (p + 2) ≤ 8192) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (monproMem s mem pa pb (p + 2) pdst) pdst (p + 2)
      (Model.montMul mm (Limbs.radix ^ (p + 2)) a b) :=
  monpro_represents s mem pa pb p pdst a b mm hn32 hpaFit hpbFit ha hb hm hodd ham hminv

/-! ## 3.  The whole call

`gasSteps_monproCsub`'s body shape, with `gasSteps_monpro` swapped for `gasSteps_fios`
and `Monpro.rowsMem` for `Fios.rowsMem`.  `Csub.gasSteps_csub` keeps its own
`hcap : rest.length ≤ 1008`, discharged from ours by `omega`. -/

def gasSteps_monproFull (s : State) (mem : ByteArray) (pa pb p : Nat) (a b mm : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (p + 2) ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (p + 2)))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (p + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (p + 2) - 32))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * (p + 2) ≤ 9472)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Challenge.EvmProof.GasSteps
      (Monpro.mpEntryState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s
        (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
        (p + 2) (p + 2) pdst ret rest) := by
  -- the three configuration words, read after the rows have run
  have hml' : MachineState.readWord
      (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 9408 =
      UInt256.ofNat (32 * (p + 2) - 32) := by
    rw [rowsMem_readWord_outside _ pa pb (p + 2) (p + 2) 9408 hn32 (Or.inr (by omega)),
      Monpro.mpZeroed_readWord_outside s mem (p + 2) 9408 (Or.inr (by omega))]
    exact hml
  have htl' : MachineState.readWord
      (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 9440 =
      UInt256.ofNat (8224 + 32 * (p + 2)) := by
    rw [rowsMem_readWord_outside _ pa pb (p + 2) (p + 2) 9440 hn32 (Or.inr (by omega)),
      Monpro.mpZeroed_readWord_outside s mem (p + 2) 9440 (Or.inr (by omega))]
    exact htl
  have hs32' : MachineState.readWord
      (Csub.csStep (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
        (p + 2) (p + 2)).memory 9344 = UInt256.ofNat (32 * (p + 2)) := by
    rw [Csub.csStep_readWord_disjoint _ (p + 2) 9344 (by omega) (Or.inr (by omega))
        (p + 2) (Nat.le_refl _),
      rowsMem_readWord_outside _ pa pb (p + 2) (p + 2) 9344 hn32 (Or.inr (by omega)),
      Monpro.mpZeroed_readWord_outside s mem (p + 2) 9344 (Or.inr (by omega))]
    exact hs32                                                                   -- ?B
  -- t[n] ≤ 1, from FIOS_MATH's `top_limb_le_one`
  have htn : (MachineState.readWord
      (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 8224).toNat ≤ 1 :=
    tn_le_one s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb hm ham hmpos hminv
  exact (gasSteps_fios s mem p pa pb pdst ret rest hcap hcode hfork hrun hnp hact
      hn32 hpa hpaFit hpb hpbFit hs32 hml htl hcds).trans
    (Csub.gasSteps_csub s
      (rowsMem (Monpro.mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) (p + 2)
      pdst ret rest (by omega) hcode hfork hrun hnp hact (by omega) hn32 hjump
      hml' htl' hs32' hdstFit
      (by rw [Csub.csStep_readWord_disjoint _ (p + 2) 8224 (by omega)
                (Or.inr (by omega)) (p + 2) (Nat.le_refl _)]
          exact htn))

/-! ## 4.  What I am unsure of -- compile these first

  BOTH `sorry`s ARE GONE.  `?A` (`row_equation`) and `?F` are closed, and `?F` is closed
  by REPLACING it: see the note on `bodyW_st`.  The statement of `fused_invariant` that
  stood here was false, not merely unproved -- it carried no `a_i · b` or `mu · m` term,
  where `Fios.st_invariant`'s right-hand side is `rowSum`, which carries both -- so I
  proved the correspondence `bodyW = Fios.st` instead.  That is also the cheaper object:
  it needs no `β ^ j` reasoning at the byte level, only `divMod` with a literal modulus,
  and it lets `st_invariant` / `rowValue_mul` / `fios_row_eq` be used exactly as they
  stand in the arithmetic file.

  All seven declarations you extracted were used, and none of the ten CIOS-only helpers
  was:  `limbSum` (+ `_congr`, `_fastRepresents`, `_succ`, `_zero`, `_eq_lowValue`),
  `add_carry_split`, `c0_spec`, `macSpec`, `readWord_storeWord_outside`,
  `Memory.readWord_writeWord`, `word_lt_size`, `word_toNat_lt'`, `mulHi_spec`
  (through `macSpec`).  `limbSum_shift` turned out NOT to be needed: `Fios.rowSum_shift`
  already does that job inside `rowValue_mul_raw`.

  NEW AND UNVERIFIED -- these are the places to look first if it does not compile:

  ?N  BLOCKING, and it is not only about this file.  `Fios.lean`, `FiosRun.lean` and
      `FiosMem.lean` are all in `…Proofs.Fast.Fios`, and three names are declared twice
      across them: `peelC1` and `peelC2` (`Fios.lean` Nat-level vs `FiosRun.lean`
      byte-level) and `rows_invariant` (`Fios.lean` Nat-level vs `FiosMem.lean`
      state-level).  `FiosRun` compiles today only because it does not import `Fios`.
      Anything that imports both cannot elaborate -- this file, and `Exp.lean` at the
      witness swap.  Fix: wrap `Fios.lean`'s body in `namespace Arith` / `end Arith`
      inside its existing `namespace Fios`.  Two lines, no proof changes; its
      declarations become `Fios.Arith.…`.  The 32 references here are already written
      `Arith.…` against that.
  ?I  the added `import …Proofs.Fast.Fios`.  Correct it if the module has another name.
  ?G  `gt_eq_lt : UInt256.gt a b = UInt256.lt b a := rfl`.  `EvmSemantics` is not in the
      tree I can read, so this is the standard definition assumed, not checked.  It is
      used in exactly two places -- `peelC2_mac` and `tailTn_toNat` -- and if `gt` is
      spelled differently those two are the only casualties.  This is the same `?1` I
      flagged when I wrote `peelC2`.
  ?R  `radix_eq : Limbs.radix = 2 ^ 256 := rfl`.  `Limbs.radix` is `def radix : Nat :=
      2 ^ 256`, so this should hold definitionally.
  ?H  I ADDED `hn2 : 2 ≤ n` to `row_equation`.  It was not provable without it (`n - 1`
      truncates at `n = 0` and the tail reads `t[n]` at 8224), and the one call site --
      `rows_invariant`, which instantiates `n := p + 2` -- now passes `(by omega)`.  That
      is the only signature change in this file.
  ?T  `tValue_rowMem` ends with `omega` on a goal that is `a + (b + c) = b + c + a` over
      three product atoms.  If `omega` refuses the nonlinear atoms, `ring` closes it, or
      `exact Nat.add_comm _ _` if the association is exactly as I expect.
  ?LV `Monpro.limbSum_eq_lowValue (memory ptr n j)` -- argument order read from
      `Monpro.lean:2091`, which is the pre-swap copy of the tree.  Same for
      `Monpro.limbSum_succ (f) (j)` and `Monpro.limbSum_congr (j) (h)`.

  STILL OPEN, unchanged from before:
  ?B  `Csub.csStep_readWord_disjoint`'s argument order -- best guess, per instruction.
  ?E  `top_limb_le_one` wants `m < beta ^ n` and I pass `hm.1`, the `FastRepresents`
      size component -- best guess, per instruction.
  ?2  `Fios.rowMem` reads `t[n]` as `8224 + 32 * n - 32 * n`.  That is now isolated in
      `rowMem_def`, which normalises it to `8224` by `omega`, so nothing downstream sees
      it.
  ?D, ?6, ?Z  RESOLVED (by you, in that order).

  Everything above section 3 -- the footprint lemma, the five `monproMem_*`, and the
  three configuration-word `have`s -- I still believe is complete and correct.
-/

end Challenge.Modexp.Submission.Proofs.Fast.Fios
