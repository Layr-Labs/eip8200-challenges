import Challenge.Modexp.Submission.Proofs.Fast.CsubReturnState
import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P3
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P4
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P5
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P6
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.Setup
import Challenge.Modexp.Submission.Proofs.Fast.Double
import Challenge.Modexp.Submission.Proofs.Fast.Ccb
import Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
import Challenge.Modexp.Submission.Proofs.Fast.R1
import Challenge.Modexp.Submission.Proofs.Fast.Lz
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P17
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P18
import Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingTraceCore

-- Keep the caller proofs in their original word normal form.
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The three driver loops of the appended Montgomery path

After `Fast.Setup` has built `R1 = R mod m` and `CC = radix * R mod m` the
appended path runs three loops and returns:

1. **the `RR` chain** (idx 1289..1324, pc 1569..1717) — six iterations of
   square-and-multiply computing `RR = φ(radix ^ n) = R² mod m`;
2. **the base chain** (idx 1325..1346, pc 1766..1824) — a Horner loop over the
   base limbs producing `ACC = b mod m`, then `BASE = MonPro(ACC, RR)`;
3. **the exponent loop** (idx 1395..1414, pc 1883..2002) — `8 * esize`
   flagless square-and-multiply steps producing `ACC = φ(b ^ e)`, the final
   `MonPro(ACC, 1)` and the `RETURN`.

`MONPRO` (pc 4667) and `ADDMOD` (pc 2347) are developed in `Fast.Monpro` and
`Fast.Csub`; here they enter only through the abstract `Subroutines` contract,
so this module does not depend on those developments.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Exp

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

-- Lean 4.31 ships `List.getElem?_cons_zero` without the `simp` attribute, so the
-- program-counter tables of `Fast.Defs` (which end in `[…][i - lo]!`) do not
-- reduce inside the block-reduction `simp` calls without it.
attribute [local simp] List.getElem?_cons_zero


theorem toNat_ofNat_self {a : Nat} (ha : a < 2 ^ 256) :
    (UInt256.ofNat a).toNat = a := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ha]


theorem isZero_ofNat_zero : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by
  decide


theorem isZero_ofNat_one : UInt256.isZero (UInt256.ofNat 1) = UInt256.ofNat 0 := by
  decide

theorem isTrue_one : UInt256.isTrue (UInt256.ofNat 1) := by decide

theorem not_isTrue_zero : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide


/-! ## The stack frame and the subroutine contracts

The five outer words `[s32, n, bsize, esize, msize]` sit at the bottom of the
stack for the whole of the appended path; every state below carries them
explicitly. -/

/-- The persistent outer frame, top first. -/
def outer (n bsize esize msize : Nat) : List UInt256 :=
  [UInt256.ofNat (32 * n), UInt256.ofNat n, UInt256.ofNat bsize,
   UInt256.ofNat esize, UInt256.ofNat msize]

-- `mpCall` -- the `MONPRO` call state at the kernel's multiply entry -- is DELETED, not
-- renumbered.  There is no multiply entry in this artifact to renumber it to.  The old
-- entry was `JUMPDEST; PUSH2 <mul row head>` falling through into `common`; that `PUSH2`
-- was HOISTED into the fused frame program at pc 3414..3454, where it is the single
-- `PUSH2 3465` in the whole 5,428-byte program (instruction index 2766).  Measured four
-- ways: instruction 2386 is pc 2919, not 3209; pc 3209 decodes to `ISZERO`;
-- `JUMPDEST; PUSH2 3465` occurs zero times; and `common` (pc 3327) is reached from exactly
-- one site in the artifact, `PUSH2 800; PUSH2 512; DUP1; DUP1; PUSH2 4480; PUSH2 3327;
-- JUMP`, which is the SQUARE call.  Nothing enters it as a multiply.
-- The `monpro` field below went with it; `mpMem`, `amMem` and `mpFrame` stay, because the
-- memory effect and frame preservation are still consumed through `SubSpec`.


/-- The `SQUARE` call state: the kernel's shared `common` block, entered with
`hd = sq_row` and all three operands at `0x800`, stack
`[sq_row, 2048, 2048, 2048, ret] ++ tail`.  The square rows address the
accumulator as `ptr + 0x1840`, which is correct only for an operand at `0x800`;
the only caller (the fixed-exponent chain) squares `0x800` in place. -/
def sqCall (s : State) (mem : ByteArray) (ret : UInt256)
    (tail : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3327
           stack := UInt256.ofNat 4480 :: UInt256.ofNat 512 :: UInt256.ofNat 512 ::
             UInt256.ofNat 512 :: ret :: tail
           memory := mem }

/-- The state a subroutine returns to. -/
def retTo (s : State) (mem : ByteArray) (ret : UInt256)
    (tail : List UInt256) : State :=
  { s with pc := ret, stack := tail, memory := mem }


/-! ### The configuration words

`V_S32 = 0x2480`, `V_MINV = 0x24A0`, `V_ML = 0x24C0`, `V_TL = 0x24E0` and
`V_EOFF = 0x2500` are written once by `Fast.Setup` and read by every
subroutine.  No transformer in the driver writes at or above `0x2480`, so the
whole bundle is preserved by a single lemma per transformer. -/
structure Frame (mem : ByteArray) (n bsize minv : Nat) : Prop where
  s32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n)
  minvW : MachineState.readWord mem 2720 = UInt256.ofNat minv
  ml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32)
  tl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n)
  eoff : MachineState.readWord mem 2816 = UInt256.ofNat (96 + bsize)

/-! ### The combined `ADDMOD` transformer

`Fast.Csub` splits the routine at pc 2470 into `gasSteps_addmod` (the schoolbook
add) and `gasSteps_csub` (the conditional subtract); the driver only ever calls
the pair.  `amMemOf` is the memory the pair leaves behind. -/

/-- The memory one `ADDMOD(pa, pb) → pd` call produces. -/
def amMemOf (mem : ByteArray) (pa pb n pd : Nat) : ByteArray :=
  Csub.csResultMemory (Csub.amResultMemory mem pa pb n) n pd

/-- `ADDMOD` writes only below `2112`, so nothing at or above `V_S32` moves. -/
theorem amMemOf_readWord_high (mem : ByteArray) (pa pb n pd addr : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hpd : pd + 32 * n ≤ 2048) (haddr : 2688 ≤ addr) :
    MachineState.readWord (amMemOf mem pa pb n pd) addr =
      MachineState.readWord mem addr := by
  rw [amMemOf,
    Double.readWord_csResultMemory_high _ n pd addr hn (by omega) (by omega) haddr,
    Double.readWord_amResultMemory_high _ pa pb n addr hn (by omega) haddr]

/-- `ADDMOD` preserves the configuration words. -/
theorem amMemOf_frame {mem : ByteArray} {n bsize minv : Nat} (pa pb pd : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hpd : pd + 32 * n ≤ 2048)
    (hf : Frame mem n bsize minv) : Frame (amMemOf mem pa pb n pd) n bsize minv := by
  have key : ∀ addr, 2688 ≤ addr →
      MachineState.readWord (amMemOf mem pa pb n pd) addr =
        MachineState.readWord mem addr :=
    fun addr haddr => amMemOf_readWord_high mem pa pb n pd addr hn hn32 hpd haddr
  exact ⟨by rw [key 2688 (by omega)]; exact hf.s32,
         by rw [key 2720 (by omega)]; exact hf.minvW,
         by rw [key 2752 (by omega)]; exact hf.ml,
         by rw [key 2784 (by omega)]; exact hf.tl,
         by rw [key 2816 (by omega)]; exact hf.eoff⟩


/-- The subroutines the driver calls, as abstract single-step contracts
carrying exactly the side conditions `Fast.CarryFull.gasSteps_monproFull`,
`Fast.SquareFull.gasSteps_squareFull` and
`Fast.Csub.gasSteps_addmod`/`gasSteps_csub` require: the configuration words
(`Frame`), the pointer bounds, the return-address jump destination, and — for
`MONPRO` and `SQUARE` — the values of the operand blocks.  The `SQUARE` fields
also carry its value contract, since `SubSpec` is shared by callers that never
square.  The concrete instance `subs` lives in `Fast.ExpSubs`, so this module
depends on neither the multiply nor the square kernel development. -/
structure Subroutines (s : State) (n bsize mm minv : Nat) where
  /-- The memory effect of `MonPro(pa, pb) → pd`. -/
  mpMem : Nat → Nat → Nat → ByteArray → ByteArray
  /-- The memory effect of `AddMod(pa, pb) → pd`. -/
  amMem : Nat → Nat → Nat → ByteArray → ByteArray
  /-- `MONPRO` preserves the configuration words. -/
  mpFrame : ∀ (pa pb pd : Nat) (mem : ByteArray), pd ≤ 1536 →
    Frame mem n bsize minv → Frame (mpMem pa pb pd mem) n bsize minv
  /-- `ADDMOD` preserves the configuration words. -/
  amFrame : ∀ (pa pb pd : Nat) (mem : ByteArray), pd ≤ 1536 →
    Frame mem n bsize minv → Frame (amMem pa pb pd mem) n bsize minv
  -- The `monpro` GasSteps field is DELETED with `mpCall` above: it was the only thing that
  -- named the multiply entry, the entry is absent from this artifact (see the note at
  -- `mpCall`), and it had ZERO consumers tree-wide once the unaccelerated per-square route
  -- was removed.  `mpMem` and `mpFrame` are retained -- the VALUE side of `MONPRO` is still
  -- live through `SubSpec`, which `ShiftCorrect`, `RootE3Correct` and `FixedDirectCorrect`
  -- all consume.  Only the control-flow contract is gone.
  /-- The memory effect of the in-place `SQUARE(0x800) → 0x800`. -/
  sqMem : ByteArray → ByteArray
  /-- `SQUARE` preserves the configuration words. -/
  sqFrame : ∀ (mem : ByteArray),
    Frame mem n bsize minv → Frame (sqMem mem) n bsize minv
  /-- `SQUARE`, entered at the kernel's `common` block with
  `hd = sq_row` and all three operands at `0x800`.

  Only for the widths the kernel does *not* accelerate: for `n ∈ {4, 8}` the
  kernel keeps its frame and loops internally (`squareLoop` below), so it never
  returns to the pushed `ret`. -/
  square : ∀ (ret : UInt256) (tail : List UInt256) (mem : ByteArray) (a : Nat),
    ¬ ((n = 4 ∨ n = 8) ∧ minv ≠ 1) → tail.length ≤ 998 →
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true →
    Frame mem n bsize minv → Model.FastRepresents mem 0 n mm →
    Model.FastRepresents mem 512 n a → a < mm →
    Challenge.EvmProof.GasSteps (sqCall s mem ret tail)
      (retTo s (sqMem mem) ret tail)
  /-- `SQUARE` writes the Montgomery square of the block at `0x800` back to
  `0x800`. -/
  sqValue : ∀ (mem : ByteArray) (a : Nat),
    Frame mem n bsize minv → Model.FastRepresents mem 0 n mm →
    Model.FastRepresents mem 512 n a → a < mm →
    Model.FastRepresents (sqMem mem) 512 n
      (Model.montMul mm (Limbs.radix ^ n) a a)
  /-- `SQUARE` leaves every other named block alone. -/
  sqKeep : ∀ (ptr v : Nat) (mem : ByteArray),
    ptr + 32 * n ≤ 1792 → (512 + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ 512) →
    Model.FastRepresents mem ptr n v →
    Model.FastRepresents (sqMem mem) ptr n v
  /-- Memory after the retained-frame square chain and mixed-domain final product. -/
  sqLoopMem : Nat → ByteArray → ByteArray
  /-- The accelerated widths complete the final product before returning to the cleanup. -/
  squareLoop : ∀ (k : Nat) (ret : UInt256) (tail : List UInt256)
    (mem : ByteArray) (a : Nat), (n = 4 ∨ n = 8) ∧ minv ≠ 1 → 1 ≤ k → k ≤ 16 →
    tail.length ≤ 982 →
    MachineState.readWord mem 2624 = UInt256.ofNat k →
    Frame mem n bsize minv → Model.FastRepresents mem 0 n mm →
    Model.FastRepresents mem 512 n a → a < mm →
    Challenge.EvmProof.GasSteps (sqCall s mem ret tail)
      (retTo s (sqLoopMem k mem) (UInt256.ofNat 782) tail)
  /-- The raw factor retained in ACC decodes the Montgomery square chain. -/
  sqLoopValue : ∀ (k : Nat) (mem : ByteArray) (a b : Nat), n = 4 ∨ n = 8 → 1 ≤ k →
    Frame mem n bsize minv → Model.FastRepresents mem 0 n mm →
    Model.FastRepresents mem 512 n a → Model.FastRepresents mem 256 n b → a < mm → b < mm →
    Model.FastRepresents (sqLoopMem k mem) 256 n
      (Model.montMul mm (Limbs.radix ^ n)
        ((fun x => Model.montMul mm (Limbs.radix ^ n) x x)^[k] a) b)

/-! ## The `RR` chain

`RRL` (pc 1569) is entered with `[k] ++ OUTER` for `k = 5, 4, …, 0`; each
iteration squares `RR` and multiplies it by `R1` or `CC` according to bit `k`
of `n`.  The selected operand address is `R1 + 1024 * bit`, i.e. `0x1000` or
`0x1400`. -/

/-- Bit `k` of `v`. -/
def bitAt (v k : Nat) : Nat := v / 2 ^ k % 2

theorem bitAt_le_one (v k : Nat) : bitAt v k ≤ 1 := by
  unfold bitAt
  omega

/-- Above its leading one a byte has only zeros. -/
theorem bitAt_gt_topExp {w k : Nat} (hw : w < 256) (hk : Lz.topExp w < k) :
    bitAt w k = 0 := by
  have hlt : w < 2 ^ k :=
    Nat.lt_of_lt_of_le (Lz.topBit_spec w hw).2.2
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold bitAt
  rw [Nat.div_eq_of_lt hlt]

/-- The branch-free operand selector: `R1` when bit `k` of `n` is clear, `CC`
when it is set. -/
def selOf (n k : Nat) : Nat := 1024 + 256 * bitAt n k

/-- `RRL`, pc 1569, at the top of iteration `k`. -/
def rrHead (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat 804
           stack := UInt256.ofNat k :: outer n bsize esize msize
           memory := mem }


/-- `BDONE`, pc 1883, where the base chain rejoins. -/
def bDone (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2396
           stack := outer n bsize esize msize
           memory := mem }


/-! ### The `RR` loop -/

@[simp] theorem outer_length (n bsize esize msize : Nat) :
    (outer n bsize esize msize).length = 5 := by
  simp [outer]


/-- One `RR` round: square, and multiply by `CC` only when bit `k` of `n` is
set.  When it is clear the selector would be `R1`, the Montgomery form of one,
so the multiply is the identity and the block skips the call. -/
def rrStep (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (n k : Nat)
    (mem : ByteArray) : ByteArray :=
  if bitAt n k = 0 then mpMem 1536 1536 1536 mem
  else mpMem 1536 1280 1536 (mpMem 1536 1536 1536 mem)

/-- The memory after `i` iterations of the `RR` chain. -/
def rrMem (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (n : Nat)
    (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | i + 1 => rrStep mpMem n (5 - i) (rrMem mpMem n mem i)


/-- The number of limbs of the base. -/
def pbOf (bsize : Nat) : Nat := (31 + bsize) / 32


/-! ### Memory writes and the active-word high-water mark

Every address the appended path touches lies below `0x2540`, so once the setup
block has stored `V_N` at `0x2520` no access here moves the high-water mark. -/

theorem mod_word_self {a : Nat} (h : a < 2 ^ 256) :
    a % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = a :=
  Nat.mod_eq_of_lt h

theorem push0_word : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide

/-- One 32-byte store. -/
def storeWord (mem : ByteArray) (addr : Nat) (w : UInt256) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w.toNat 32) addr

/-- One `MCOPY`. -/
def mcopyMem (mem : ByteArray) (dst src sz : Nat) : ByteArray :=
  MachineState.writeBytes mem (MachineState.readPadded mem src sz) dst

theorem readWord_mcopyMem_disjoint (mem : ByteArray) (dst src sz a : Nat)
    (hdisj : a + 32 ≤ dst ∨ dst + sz ≤ a) :
    MachineState.readWord (mcopyMem mem dst src sz) a =
      MachineState.readWord mem a := by
  refine Challenge.EvmProof.Memory.readWord_writeBytes_disjoint mem _ a dst ?_
  rw [Challenge.EvmProof.Memory.readPadded_size]
  exact hdisj

/-- `Csub.fastRepresents_mcopy` in `mcopyMem` shape. -/
theorem fastRepresents_mcopyMem (mem : ByteArray) (dst src n v : Nat) (hn : 1 ≤ n)
    (hrep : Model.FastRepresents mem src n v) :
    Model.FastRepresents (mcopyMem mem dst src (32 * n)) dst n v :=
  Csub.fastRepresents_mcopy mem src dst n v hn hrep

/-- `Csub.fastRepresents_mcopy_disjoint` in `mcopyMem` shape. -/
theorem fastRepresents_mcopyMem_disjoint (mem : ByteArray) (dst src sz ptr cnt v : Nat)
    (hdisj : dst + sz ≤ ptr ∨ ptr + 32 * cnt ≤ dst)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (mcopyMem mem dst src sz) ptr cnt v :=
  Csub.fastRepresents_mcopy_disjoint mem src dst sz ptr cnt v hdisj hrep

theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 2848) (hcurr : 89 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  have hle : (off + sz - 1) / 32 + 1 ≤ curr := by omega
  exact Nat.max_eq_left hle

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 2848) (hact : 89 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

theorem activeWords_fix2 (s : State) (off1 sz1 off2 sz2 : Nat)
    (hsz1 : sz1 ≠ 0) (hsz2 : sz2 ≠ 0)
    (hoff1 : off1 + sz1 ≤ 2848) (hoff2 : off2 + sz2 ≤ 2848)
    (hact : 89 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat off1 sz1) off2 sz2) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off1 sz1 hsz1 hoff1 hact,
    activeWordsAfter_fix _ off2 sz2 hsz2 hoff2 hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm


/-- The base limb iteration `j` stores into `ONE`: limb `pb - 1 - j` counted
from the least significant. -/
def baseLimbWord (input : ByteArray) (bsize pb j : Nat) : UInt256 :=
  MachineState.readWord input (96 + (bsize - 32 * (pb - j)))


/-- The memory after `t` iterations of the Horner loop. -/
def blMems (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (input : ByteArray) (n bsize pb : Nat) (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | t + 1 =>
      amMem 256 768 256
        (storeWord (mpMem 256 1280 256 (blMems mpMem amMem input n bsize pb mem t))
          (736 + 32 * n) (baseLimbWord input bsize pb (t + 1)))


/-! ## The exponent loop

`EB` (pc 1838) walks the `esize` exponent bytes; for each byte `EBIT`
(pc 1916) walks its eight bits from the most significant, squaring `ACC` on
every bit and multiplying by `BASE` on set bits. -/

/-- Exponent byte `i`, counted from the most significant. -/
def expByte (input : ByteArray) (bsize i : Nat) : Nat :=
  (YulSemantics.EVM.byteFrom input.toList (96 + bsize + i)).toNat

/-- `EB`, pc 1838, at the top of exponent byte `i`. -/
def ebHead (s : State) (mem : ByteArray) (n bsize esize msize i : Nat) : State :=
  { s with pc := UInt256.ofNat 950
           stack := UInt256.ofNat i :: outer n bsize esize msize
           memory := mem }


/-- pc 1938, back from the final `MonPro(ACC, ONE)`. -/
def finHead (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 784
           stack := outer n bsize esize msize
           memory := mem }

/-- The halted state after `RETURN`. -/
def returnedState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  { s with pc := UInt256.ofNat 793
           stack := outer n bsize esize msize
           memory := mem
           halt := .Returned
           hReturn := MachineState.readPadded mem (256 + 32 * n - msize) msize }


/-! Program-counter certificates for `blk1333` (instruction indices 566..573,
pc 784..793).  `Fast.Defs` used to cover these with a `fastPC` range lemma, which
was dropped when the unroll made its index range non-contiguous; these are the
individual facts the block reduction actually needs, in the same form
`Fast.Setup` uses for `blk1341`/`blk1351`.  Transcribed from the decode of the
5,428-byte artifact `fe8e9f61e6d3764a`, where indices 566..573 read
JUMPDEST, DUP5, DUP1, DUP3, PUSH2 0x100, ADD, SUB, RETURN -- matching `blk1333`
instruction for instruction.  In this image the block's leading `JUMPDEST` at pc 784 is
removed (it was reached only by fall-through), so the block starts at the `DUP5` at 784
(index 554) and the `PUSH3 0x100` at 787 runs to 791. -/
private theorem pcIdx567 :
    Artifact.submissionArtifact.instructionPC 554 = 784 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem pcIdx568 :
    Artifact.submissionArtifact.instructionPC 555 = 785 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem pcIdx569 :
    Artifact.submissionArtifact.instructionPC 556 = 786 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem pcIdx570 :
    Artifact.submissionArtifact.instructionPC 557 = 787 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem pcIdx571 :
    Artifact.submissionArtifact.instructionPC 558 = 791 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem pcIdx572 :
    Artifact.submissionArtifact.instructionPC 559 = 792 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

private theorem pcIdx573 :
    Artifact.submissionArtifact.instructionPC 560 = 793 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

set_option linter.unusedSimpArgs false in
/-- `blk1333` (instruction indices 566..573, pc 784..793):
`RETURN(ACC + s32 - msize, msize)`. -/
theorem run_return (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hm : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hact : 89 ≤ s.activeWords.toNat) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1333
      (finHead s mem n bsize esize msize) =
      some (returnedState s mem n bsize esize msize) := by
  have hsub : UInt256.ofNat (256 + 32 * n) - UInt256.ofNat msize =
      UInt256.ofNat (256 + 32 * n - msize) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega)
      (Nat.lt_of_le_of_lt (show 256 + 32 * n ≤ 512 by omega) (by norm_num))
  have hmodOff : (256 + 32 * n - msize) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 256 + 32 * n - msize :=
    mod_word_self (Nat.lt_of_le_of_lt
      (show 256 + 32 * n - msize ≤ 512 by omega) (by norm_num))
  have hmodSz : msize %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = msize :=
    mod_word_self (Nat.lt_of_le_of_lt (show msize ≤ 256 by omega) (by norm_num))
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (256 + 32 * n - msize) msize) = s.activeWords :=
    activeWords_fix s (256 + 32 * n - msize) msize (by omega) (by omega) hact
  simp (config := { maxSteps := 600000 }) [blk1333, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    finHead, returnedState, outer, hrun, hsub, hmodOff, hmodSz, hfix,
    pcIdx567, pcIdx568, pcIdx569, pcIdx570, pcIdx571, pcIdx572, pcIdx573,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]


def gasSteps_return (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hm : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hact : 89 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (finHead s mem n bsize esize msize)
      (returnedState s mem n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1333 hcode hfork
      (run_return s mem n bsize esize msize hn hn32 hm hm32 hact hrun) hrun hnp


/-! ### The bit loop -/

/-- The memory after one exponent bit. -/
def bitStep (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (mem : ByteArray) :
    Nat → ByteArray
  | 0 => mpMem 256 256 256 mem
  | _ + 1 => mpMem 256 512 256 (mpMem 256 256 256 mem)


/-- The memory after `k` bits of exponent byte `w`, started at bit index `j0`. -/
def bitMemsFrom (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (w : Nat)
    (mem : ByteArray) (j0 : Nat) : Nat → ByteArray
  | 0 => mem
  | k + 1 => bitStep mpMem (bitMemsFrom mpMem w mem j0 k) (bitAt w (7 - (j0 + k)))

/-- How many leading bits of exponent byte `i` the loop skips: byte `0` starts
at its highest set bit, every other byte at bit 7. -/
def lzSkip (input : ByteArray) (bsize i : Nat) : Nat :=
  if i = 0 then 7 - Lz.topExp (expByte input bsize i) else 0

theorem lzSkip_le (input : ByteArray) (bsize i : Nat) : lzSkip input bsize i ≤ 7 := by
  unfold lzSkip; split <;> omega

/-- The memory after exponent byte `i`, with its leading bits skipped. -/
def byteMemAt (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (input : ByteArray)
    (bsize n : Nat) (mem : ByteArray) (i : Nat) : ByteArray :=
  if i = 0 ∧ expByte input bsize i ≠ 0 then
    bitMemsFrom mpMem (expByte input bsize i) (mcopyMem mem 256 512 (32 * n))
      (lzSkip input bsize i + 1) (7 - lzSkip input bsize i)
  else
    bitMemsFrom mpMem (expByte input bsize i) mem (lzSkip input bsize i)
      (8 - lzSkip input bsize i)

/-- The memory after `i` exponent bytes. -/
def ebMems (mpMem : Nat → Nat → Nat → ByteArray → ByteArray) (input : ByteArray)
    (bsize n : Nat) (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | i + 1 => byteMemAt mpMem input bsize n (ebMems mpMem input bsize n mem i) i


/-! ### Preservation of `V_EOFF` across the exponent loop -/

theorem readWord_bitStep (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (addr : Nat)
    (hkeep : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 256 mem') addr =
        MachineState.readWord mem' addr)
    (mem : ByteArray) (bit : Nat) :
    MachineState.readWord (bitStep mpMem mem bit) addr =
      MachineState.readWord mem addr := by
  cases bit with
  | zero => exact hkeep 256 256 mem
  | succ k =>
      show MachineState.readWord (mpMem 256 512 256 (mpMem 256 256 256 mem))
        addr = _
      rw [hkeep 256 512 _, hkeep 256 256 mem]


theorem readWord_bitMemsFrom (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (addr : Nat)
    (hkeep : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 256 mem') addr =
        MachineState.readWord mem' addr)
    (w : Nat) (mem : ByteArray) (j0 k : Nat) :
    MachineState.readWord (bitMemsFrom mpMem w mem j0 k) addr =
      MachineState.readWord mem addr := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show MachineState.readWord (bitStep mpMem (bitMemsFrom mpMem w mem j0 k)
        (bitAt w (7 - (j0 + k)))) addr = _
      rw [readWord_bitStep mpMem addr hkeep _ _, ih]

theorem readWord_ebMems (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (addr : Nat)
    (hkeep : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 256 mem') addr =
        MachineState.readWord mem' addr)
    (input : ByteArray) (bsize n : Nat) (mem : ByteArray) (i : Nat)
    (haddr : 512 ≤ addr) (hn32 : n ≤ 8) :
    MachineState.readWord (ebMems mpMem input bsize n mem i) addr =
      MachineState.readWord mem addr := by
  induction i with
  | zero => rfl
  | succ i ih =>
      show MachineState.readWord (byteMemAt mpMem input bsize n
        (ebMems mpMem input bsize n mem i) i) addr = _
      rw [byteMemAt]
      split
      · rw [readWord_bitMemsFrom mpMem addr hkeep,
          readWord_mcopyMem_disjoint _ 256 512 (32 * n) addr (Or.inr (by omega)), ih]
      · rw [readWord_bitMemsFrom mpMem addr hkeep, ih]


/-! ## The returned byte string

`RETURN(ACC + s32 - msize, msize)` slices the last `msize` bytes of the `ACC`
block.  Because the block is a big-endian `32 * n`-byte encoding, that slice is
exactly the big-endian `msize`-byte encoding of the value it holds — and the
`32 * n - msize` bytes it drops are all zero. -/

theorem byteFrom_eq_getD (bs : ByteArray) (i : Nat) :
    YulSemantics.EVM.byteFrom bs.toList i = bs[i]?.getD 0 := by
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, YulEvmCompiler.ByteArray.toList_eq_data,
    Array.getElem?_toList]
  rfl

theorem memoryLimbs_succ (mem : ByteArray) (ptr count : Nat) :
    Limbs.memoryLimbs mem ptr (count + 1) =
      (MachineState.readWord mem ptr).toNat ::
        Limbs.memoryLimbs mem (ptr + 32) count := by
  apply List.ext_getElem
  · simp
  · intro k hk _
    have hk1 : k < count + 1 := by simpa using hk
    cases k with
    | zero => simp [Limbs.memoryLimbs]
    | succ j =>
        have hj : j < count := by omega
        simp only [Limbs.memoryLimbs, List.getElem_cons_succ, List.getElem_map,
          List.getElem_range]
        rw [show ptr + 32 * (j + 1) = ptr + 32 + 32 * j from by omega]

theorem fastLimbs_succ (mem : ByteArray) (ptr count : Nat) :
    Model.fastLimbs mem ptr (count + 1) =
      Model.fastLimbs mem (ptr + 32) count ++
        [(MachineState.readWord mem ptr).toNat] := by
  rw [Model.fastLimbs_eq_reverse_memoryLimbs, Model.fastLimbs_eq_reverse_memoryLimbs,
    memoryLimbs_succ, List.reverse_cons]

/-- The `32 * count` bytes of a limb block, read big-endian, are its value. -/
theorem bytesToNatPadded_block (mem : ByteArray) : ∀ (count ptr : Nat),
    Precompile.bytesToNatPadded mem ptr (32 * count) =
      Nat.ofDigits Limbs.radix (Model.fastLimbs mem ptr count) := by
  intro count
  induction count with
  | zero => intro ptr; simp [Model.fastLimbs]
  | succ c ih =>
      intro ptr
      have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add mem ptr 32 (32 * c)
      rw [show 32 + 32 * c = 32 * (c + 1) by ring] at hsplit
      rw [hsplit, fastLimbs_succ, Nat.ofDigits_append, Model.length_fastLimbs,
        ih (ptr + 32), Nat.ofDigits_singleton,
        ← Challenge.EvmProof.Bytes.readWord_toNat, ← Limbs.pow_radix]
      ring

theorem bytesToNatPadded_of_fastRepresents {mem : ByteArray} {ptr count value : Nat}
    (hrep : Model.FastRepresents mem ptr count value) :
    Precompile.bytesToNatPadded mem ptr (32 * count) = value := by
  rw [bytesToNatPadded_block mem count ptr, Model.value_of_fastRepresents hrep]


/-- Byte `k` of a big-endian read. -/
theorem bytesToNatPadded_digit (bs : ByteArray) (off w k : Nat) (hk : k < w) :
    Precompile.bytesToNatPadded bs off w / 256 ^ (w - 1 - k) % 256 =
      (YulSemantics.EVM.byteFrom bs.toList (off + k)).toNat := by
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add bs off (k + 1)
    (w - (k + 1))
  rw [show k + 1 + (w - (k + 1)) = w from by omega] at hsplit
  have htail := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow bs (off + (k + 1))
    (w - (k + 1))
  have hsplit' : Precompile.bytesToNatPadded bs off w =
      256 ^ (w - (k + 1)) * Precompile.bytesToNatPadded bs off (k + 1) +
        Precompile.bytesToNatPadded bs (off + (k + 1)) (w - (k + 1)) := by
    rw [hsplit]; ring
  have hdiv : Precompile.bytesToNatPadded bs off w / 256 ^ (w - 1 - k) =
      Precompile.bytesToNatPadded bs off (k + 1) := by
    rw [show w - 1 - k = w - (k + 1) from by omega, hsplit',
      Nat.mul_add_div (pow_pos (by norm_num) _), Nat.div_eq_of_lt htail,
      Nat.add_zero]
  have hb : (YulSemantics.EVM.byteFrom bs.toList (off + k)).toNat < 256 :=
    (YulSemantics.EVM.byteFrom bs.toList (off + k)).toNat_lt
  rw [hdiv, Challenge.EvmProof.Bytes.bytesToNatPadded_succ bs off k]
  omega

theorem uint8_ofNat_toNat (b : UInt8) : UInt8.ofNat b.toNat = b := by
  simp

/-- **The returned slice.**  The last `msize` bytes of a block holding `value`
are the big-endian `msize`-byte encoding of `value`. -/
theorem readPadded_eq_natToBytes {mem : ByteArray} {ptr count value msize : Nat}
    (hrep : Model.FastRepresents mem ptr count value) (hm : msize ≤ 32 * count) :
    MachineState.readPadded mem (ptr + 32 * count - msize) msize =
      Precompile.natToBytes value msize := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size, Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro k hleft hright
    have hk : k < msize := by
      simpa [Precompile.natToBytes,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hright
    have hdig := bytesToNatPadded_digit mem ptr (32 * count)
      (32 * count - msize + k) (by omega)
    rw [bytesToNatPadded_of_fastRepresents hrep,
      show 32 * count - 1 - (32 * count - msize + k) = msize - 1 - k from by omega]
      at hdig
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hk,
      Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ msize k hk,
      show ptr + 32 * count - msize + k = ptr + (32 * count - msize + k) from by omega,
      ← byteFrom_eq_getD, hdig, uint8_ofNat_toNat]

/-- **The `RETURN` payload is the specification.** -/
theorem returned_eq_spec (s : State) (mem input : ByteArray)
    (n bsize esize msize result : Nat) (_hn : 2 ≤ n) (hm : msize ≤ 32 * n)
    (hmpos : 0 < msize)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hrep : Model.FastRepresents mem 256 n result)
    (hres : result = Precompile.modPow
      (Precompile.bytesToNatPadded input 96 bsize)
      (Precompile.bytesToNatPadded input (96 + bsize) esize)
      (Precompile.bytesToNatPadded input (96 + bsize + esize) msize)) :
    (returnedState s mem n bsize esize msize).hReturn = Challenge.Modexp.spec input := by
  have hslice := readPadded_eq_natToBytes hrep hm
  have hspec : Challenge.Modexp.spec input =
      Precompile.natToBytes (Precompile.modPow
        (Precompile.bytesToNatPadded input 96 bsize)
        (Precompile.bytesToNatPadded input (96 + bsize) esize)
        (Precompile.bytesToNatPadded input (96 + bsize + esize) msize)) msize := by
    simp only [Challenge.Modexp.spec, ← hbsize, ← hesize, ← hmsz]
    exact if_neg (by omega)
  show MachineState.readPadded mem (256 + 32 * n - msize) msize = _
  rw [hslice, hspec, hres]

/-! ## The exponent bridge

The bits the loop consumes are exactly the big-endian bits of
`Precompile.bytesToNatPadded input (96 + bsize) esize`. -/

/-- Exponent byte `i` is digit `i` of the exponent. -/
theorem expByte_eq_digit (input : ByteArray) (bsize esize i : Nat) (hi : i < esize) :
    expByte input bsize i =
      Precompile.bytesToNatPadded input (96 + bsize) esize /
        256 ^ (esize - 1 - i) % 256 :=
  (bytesToNatPadded_digit input (96 + bsize) esize i hi).symm

/-- Bit `r` of exponent byte `i` is bit `8 * (esize - 1 - i) + r` of the
exponent. -/
theorem bitAt_expByte (input : ByteArray) (bsize esize i r : Nat)
    (hi : i < esize) (hr : r < 8) :
    bitAt (expByte input bsize i) r =
      bitAt (Precompile.bytesToNatPadded input (96 + bsize) esize)
        (8 * (esize - 1 - i) + r) := by
  have h256 : (256 : Nat) ^ (esize - 1 - i) = 2 ^ (8 * (esize - 1 - i)) := by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
  have hsplit : (2 : Nat) ^ 8 = 2 ^ r * 2 ^ (8 - r) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [expByte_eq_digit input bsize esize i hi, bitAt, bitAt, h256,
    show (256 : Nat) = 2 ^ 8 by norm_num, hsplit, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega)), Nat.div_div_eq_div_mul,
    ← pow_add]


/-- One left-to-right step of the accumulated exponent. -/
theorem expPrefix_step (e B t : Nat) (ht : t < B) :
    Model.expPrefix e (B - t - 1) =
      2 * Model.expPrefix e (B - t) + bitAt e (B - t - 1) := by
  have h := Model.expPrefix_succ e (B - t - 1)
  rwa [show B - t - 1 + 1 = B - t from by omega] at h


/-! ## The arithmetic of the three loops

Neither `MONPRO` nor `ADDMOD` has a functional contract in this module, so what
each loop computes is stated in the arithmetic model — `Model.montMul` for the
Montgomery product and `(a + b) % m` for the modular addition.  Composing these
recursions with `Fast.Monpro`'s and `Fast.Csub`'s correctness statements gives
the memory-level postconditions. -/

/-- The value the `RR` block holds after `i` iterations of the `RR` chain:
square, then multiply by `R1` or `CC` according to bit `5 - i` of `n`. -/
def rrValue (mm R n : Nat) : Nat → Nat
  | 0 => R % mm
  | i + 1 =>
      Model.montMul mm R
        (Model.montMul mm R (rrValue mm R n i) (rrValue mm R n i))
        (if bitAt n (5 - i) = 0 then R % mm else Limbs.radix * R % mm)

theorem rrValue_succ (mm R n i : Nat) :
    rrValue mm R n (i + 1) =
      Model.montMul mm R
        (Model.montMul mm R (rrValue mm R n i) (rrValue mm R n i))
        (if bitAt n (5 - i) = 0 then R % mm else Limbs.radix * R % mm) := rfl

/-- `R1` is the Montgomery form of one, so multiplying by it does nothing. -/
theorem montMul_by_one {mm R x : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hx : x < mm) : Model.montMul mm R x (R % mm) = x :=
  Model.montMul_eq_of_modEq hm hcop
    (Nat.ModEq.mul_left x (Nat.mod_modEq R mm).symm) hx

/-- **The `RR` chain invariant.**  After `i` iterations the block holds the
Montgomery form of `radix ^ (n >>> (6 - i))`. -/
theorem rrValue_form {mm R : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    {n : Nat} (hn : n ≤ 8) : ∀ i, i ≤ 6 →
    rrValue mm R n i ≡ Limbs.radix ^ (n / 2 ^ (6 - i)) * R [MOD mm] := by
  intro i
  induction i with
  | zero =>
      intro _
      have h64 : n / 2 ^ (6 - 0) = 0 := by
        apply Nat.div_eq_of_lt
        have : (2 : Nat) ^ (6 - 0) = 64 := by norm_num
        omega
      rw [h64, pow_zero, one_mul]
      exact Nat.mod_modEq R mm
  | succ i ih =>
      intro hi
      have hv := ih (by omega)
      have hsq := Model.montMul_form hm hcop hv hv
      have hpow : Limbs.radix ^ (n / 2 ^ (6 - i)) * Limbs.radix ^ (n / 2 ^ (6 - i)) =
          Limbs.radix ^ (2 * (n / 2 ^ (6 - i))) := by
        rw [two_mul, pow_add]
      have hx : Limbs.radix ^ (n / 2 ^ (6 - i)) * Limbs.radix ^ (n / 2 ^ (6 - i)) * R
          % mm ≡ Limbs.radix ^ (2 * (n / 2 ^ (6 - i))) * R [MOD mm] := by
        rw [hpow]
        exact Nat.mod_modEq _ mm
      have hsel : (if bitAt n (5 - i) = 0 then R % mm else Limbs.radix * R % mm) ≡
          Limbs.radix ^ bitAt n (5 - i) * R [MOD mm] := by
        by_cases h0 : bitAt n (5 - i) = 0
        · rw [if_pos h0, h0, pow_zero, one_mul]
          exact Nat.mod_modEq R mm
        · have h1 : bitAt n (5 - i) = 1 := by
            have := bitAt_le_one n (5 - i)
            omega
          rw [if_neg h0, h1, pow_one]
          exact Nat.mod_modEq _ mm
      have hstep : n / 2 ^ (6 - (i + 1)) =
          2 * (n / 2 ^ (6 - i)) + bitAt n (5 - i) := by
        have h := Model.expPrefix_succ n (5 - i)
        rw [show 6 - (i + 1) = 5 - i from by omega]
        rw [Model.expPrefix, Model.expPrefix,
          show 5 - i + 1 = 6 - i from by omega] at h
        exact h
      rw [rrValue_succ, hsq, Model.montMul_form hm hcop hx hsel, hstep, pow_add]
      exact Nat.mod_modEq _ mm

/-- **The `RR` chain postcondition.**  Six iterations leave the Montgomery form
of `radix ^ n`; taking `R = radix ^ n mod m` this is `R ^ 2 mod m`. -/
theorem rrValue_final {mm R : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    {n : Nat} (hn : n ≤ 8) :
    rrValue mm R n 6 ≡ Limbs.radix ^ n * R [MOD mm] := by
  have h := rrValue_form hm hcop hn 6 le_rfl
  rwa [show (6 : Nat) - 6 = 0 from rfl, pow_zero, Nat.div_one] at h

/-- The value `ACC` holds after `t` Horner steps over the `pb` base limbs. -/
def blValue (mm b pb : Nat) : Nat → Nat
  | 0 => b / Limbs.radix ^ (pb - 1) % mm
  | t + 1 =>
      (blValue mm b pb t * Limbs.radix % mm +
        b / Limbs.radix ^ (pb - 1 - (t + 1)) % Limbs.radix) % mm

theorem blValue_succ (mm b pb t : Nat) :
    blValue mm b pb (t + 1) =
      (blValue mm b pb t * Limbs.radix % mm +
        b / Limbs.radix ^ (pb - 1 - (t + 1)) % Limbs.radix) % mm := rfl

/-- **The Horner invariant.**  After `t` steps the accumulator holds the top
`t + 1` limbs of the base, reduced. -/
theorem blValue_eq (mm b pb : Nat) : ∀ t, t < pb →
    blValue mm b pb t = b / Limbs.radix ^ (pb - 1 - t) % mm := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      have hk : pb - 1 - t = pb - 1 - (t + 1) + 1 := by omega
      rw [blValue_succ, ih (by omega), hk]
      exact Model.horner_div_step mm b (pb - 1 - (t + 1))

/-- **The base-chain postcondition.**  After `pb - 1` steps the accumulator is
`b mod m`. -/
theorem blValue_final (mm b pb : Nat) (hpb : 1 ≤ pb) :
    blValue mm b pb (pb - 1) = b % mm := by
  rw [blValue_eq mm b pb (pb - 1) (by omega),
    show pb - 1 - (pb - 1) = 0 from by omega, pow_zero, Nat.div_one]

/-- The accumulator after `t` exponent bits. -/
def expAcc (mm R bM : Nat) (bits : Nat → Nat) : Nat → Nat
  | 0 => R % mm
  | t + 1 =>
      if bits t = 0 then
        Model.montMul mm R (expAcc mm R bM bits t) (expAcc mm R bM bits t)
      else
        Model.montMul mm R
          (Model.montMul mm R (expAcc mm R bM bits t) (expAcc mm R bM bits t)) bM

theorem expAcc_succ (mm R bM : Nat) (bits : Nat → Nat) (t : Nat) :
    expAcc mm R bM bits (t + 1) =
      if bits t = 0 then
        Model.montMul mm R (expAcc mm R bM bits t) (expAcc mm R bM bits t)
      else
        Model.montMul mm R
          (Model.montMul mm R (expAcc mm R bM bits t) (expAcc mm R bM bits t)) bM :=
  rfl

/-- The exponent the loop has accumulated after `t` bits. -/
def expExp (bits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => 2 * expExp bits t + bits t

/-- **The exponent-loop invariant.**  The accumulator is the Montgomery form of
`b ^ E` for the exponent `E` accumulated so far. -/
theorem expAcc_form {mm R b bM : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hbM : bM ≡ b * R [MOD mm]) (bits : Nat → Nat) (hbits : ∀ t, bits t ≤ 1) :
    ∀ t, expAcc mm R bM bits t ≡ b ^ expExp bits t * R [MOD mm] := by
  intro t
  induction t with
  | zero => exact Model.mont_pow_zero_form mm R b
  | succ t ih =>
      rw [expAcc_succ, Model.mont_bit_step hm hcop ih hbM (hbits t)]
      exact Nat.mod_modEq _ mm

/-- **The exponent bridge.**  Consuming the big-endian bits of `e` accumulates
exactly `e`. -/
theorem expExp_eq_prefix {e B : Nat} (he : e < 2 ^ B) (bits : Nat → Nat)
    (hbits : ∀ t, t < B → bits t = bitAt e (B - t - 1)) :
    ∀ t, t ≤ B → expExp bits t = Model.expPrefix e (B - t) := by
  intro t
  induction t with
  | zero => intro _; exact (Model.expPrefix_top he).symm
  | succ t ih =>
      intro ht
      show 2 * expExp bits t + bits t = _
      rw [ih (by omega), hbits t (by omega),
        show B - (t + 1) = B - t - 1 from by omega]
      exact (expPrefix_step e B t (by omega)).symm

theorem expExp_eq {e B : Nat} (he : e < 2 ^ B) (bits : Nat → Nat)
    (hbits : ∀ t, t < B → bits t = bitAt e (B - t - 1)) :
    expExp bits B = e := by
  have h := expExp_eq_prefix he bits hbits B le_rfl
  rwa [Nat.sub_self, Model.expPrefix_zero] at h

/-- **The final conversion.**  `MonPro(ACC, 1)` on the Montgomery form of
`b ^ e` yields the precompile's answer. -/
theorem expAcc_out {mm R b bM : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hbM : bM ≡ b * R [MOD mm]) (bits : Nat → Nat) (hbits : ∀ t, bits t ≤ 1)
    {e B : Nat} (he : e < 2 ^ B)
    (hbit : ∀ t, t < B → bits t = bitAt e (B - t - 1)) :
    Model.montMul mm R (expAcc mm R bM bits B) 1 =
      Precompile.modPow b e mm := by
  have hform := expAcc_form hm hcop hbM bits hbits B
  rw [expExp_eq he bits hbit] at hform
  exact Model.mont_out_modPow hm hcop hform

/-! ## Memory-level postconditions of the three loops

The two subroutines enter through the functional contract `SubSpec`; composing
it with the value recursions above turns each loop's arithmetic invariant into
a statement about the named blocks. -/

/-- Functional contract for `MONPRO` and `ADDMOD` at `n` limbs, modulus `mm`.
`Fast.Monpro` and `Fast.Csub` supply it. -/
structure SubSpec (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (n mm R minv : Nat) : Prop where
  /-- `MonPro(pa, pb) → pd` writes the Montgomery product.  The pointer bounds
  and the `V_MINV` word are exactly the memory-dependent hypotheses
  `Fast.Monpro.monpro_represents` takes; its constant side conditions
  (`2 ≤ n ≤ 8`, `m` odd, and `m % radix * minv + 1 ≡ 0 [MOD 2 ^ 256]`) are
  supplied once by whoever builds this record. -/
  mpValueRaw : ∀ (pa pb pd : Nat) (mem : ByteArray) (a b : Nat),
    pa + 32 * n ≤ 2048 → pb + 32 * n ≤ 2048 → pd + 32 * n ≤ 2048 →
    Model.FastRepresents mem 0 n mm →
    MachineState.readWord mem 2720 = UInt256.ofNat minv →
    Model.FastRepresents mem pa n a → Model.FastRepresents mem pb n b →
    a < mm →
    Model.FastRepresents (mpMem pa pb pd mem) pd n (Model.montMul mm R a b)
  /-- `MonPro` leaves every other named block alone. -/
  mpFrame : ∀ (pa pb pd ptr v : Nat) (mem : ByteArray),
    ptr + 32 * n ≤ 1792 → (pd + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ pd) →
    Model.FastRepresents mem ptr n v →
    Model.FastRepresents (mpMem pa pb pd mem) ptr n v
  /-- `MonPro` writes nothing at or above `V_MINV = 0x24A0`. -/
  mpMinv : ∀ (pa pb pd : Nat) (mem : ByteArray), pd ≤ 1536 →
    MachineState.readWord (mpMem pa pb pd mem) 2720 = MachineState.readWord mem 2720
  /-- `AddMod(pa, pb) → pd` writes the modular sum. -/
  amValue : ∀ (pa pb pd : Nat) (mem : ByteArray) (a b : Nat),
    pa + 32 * n ≤ 2048 → pb + 32 * n ≤ 2048 → pd + 32 * n ≤ 2048 →
    Model.FastRepresents mem 0 n mm →
    Model.FastRepresents mem pa n a → Model.FastRepresents mem pb n b →
    a + b < 2 * mm →
    Model.FastRepresents (amMem pa pb pd mem) pd n ((a + b) % mm)
  /-- `AddMod` leaves every other named block alone. -/
  amFrame : ∀ (pa pb pd ptr v : Nat) (mem : ByteArray),
    ptr + 32 * n ≤ 1792 → (pd + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ pd) →
    Model.FastRepresents mem ptr n v →
    Model.FastRepresents (amMem pa pb pd mem) ptr n v
  /-- `AddMod` writes nothing at or above `V_MINV = 0x24A0`. -/
  amMinv : ∀ (pa pb pd : Nat) (mem : ByteArray), pd ≤ 1536 →
    MachineState.readWord (amMem pa pb pd mem) 2720 = MachineState.readWord mem 2720

/-- Reduced-operand compatibility view of the stronger CIOS contract.
The second operand need only fit its represented limb region. -/
theorem SubSpec.mpValue {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv)
    (pa pb pd : Nat) (mem : ByteArray) (a b : Nat)
    (hpa : pa + 32 * n ≤ 2048) (hpb : pb + 32 * n ≤ 2048)
    (hpd : pd + 32 * n ≤ 2048) (hm : Model.FastRepresents mem 0 n mm)
    (hminv : MachineState.readWord mem 2720 = UInt256.ofNat minv)
    (ha : Model.FastRepresents mem pa n a) (hb : Model.FastRepresents mem pb n b)
    (ham : a < mm) (_hbm : b < mm) :
    Model.FastRepresents (mpMem pa pb pd mem) pd n (Model.montMul mm R a b) :=
  spec.mpValueRaw pa pb pd mem a b hpa hpb hpd hm hminv ha hb ham

theorem rrValue_lt {mm R n : Nat} (hm : 0 < mm) : ∀ i, rrValue mm R n i < mm := by
  intro i
  cases i with
  | zero => exact Nat.mod_lt _ hm
  | succ i => exact Model.montMul_lt hm _ _ _

/-- The four blocks the `RR` chain reads and writes. -/
structure RrInv (mem : ByteArray) (n mm R v : Nat) : Prop where
  modulus : Model.FastRepresents mem 0 n mm
  r1 : Model.FastRepresents mem 1024 n (R % mm)
  cc : Model.FastRepresents mem 1280 n (Limbs.radix * R % mm)
  rr : Model.FastRepresents mem 1536 n v

/-- `V_MINV` survives the `RR` chain. -/
theorem readWord_rrMem (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (hkeep : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 1536 mem') 2720 =
        MachineState.readWord mem' 2720)
    (n : Nat) (mem : ByteArray) (i : Nat) :
    MachineState.readWord (rrMem mpMem n mem i) 2720 =
      MachineState.readWord mem 2720 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      show MachineState.readWord (rrStep mpMem n (5 - i) (rrMem mpMem n mem i))
        2720 = _
      unfold rrStep
      split
      · rw [hkeep 1536 1536 _, ih]
      · rw [hkeep 1536 1280 _, hkeep 1536 1536 _, ih]

set_option maxHeartbeats 16000000 in
/-- **The `RR` chain, at the level of memory.** -/
theorem rrMem_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hcop : Nat.Coprime R mm)
    (hn32 : n ≤ 8) (mem : ByteArray)
    (hminv : MachineState.readWord mem 2720 = UInt256.ofNat minv)
    (hinv : RrInv mem n mm R (R % mm)) : ∀ i,
    RrInv (rrMem mpMem n mem i) n mm R (rrValue mm R n i) := by
  intro i
  induction i with
  | zero => exact hinv
  | succ i ih =>
      have hv : rrValue mm R n i < mm := rrValue_lt hm i
      have hsellb : selOf n (5 - i) ≤ 1280 := by
        have := bitAt_le_one n (5 - i)
        unfold selOf
        omega
      have hmi : MachineState.readWord (rrMem mpMem n mem i) 2720 =
          UInt256.ofNat minv :=
        (readWord_rrMem mpMem
          (fun pa pb m => spec.mpMinv pa pb 1536 m (by omega)) n mem i).trans hminv
      have hmi1 : MachineState.readWord
          (mpMem 1536 1536 1536 (rrMem mpMem n mem i)) 2720 = UInt256.ofNat minv :=
        (spec.mpMinv 1536 1536 1536 _ (by omega)).trans hmi
      have hsq : Model.FastRepresents (mpMem 1536 1536 1536 (rrMem mpMem n mem i))
          1536 n (Model.montMul mm R (rrValue mm R n i) (rrValue mm R n i)) :=
        spec.mpValue 1536 1536 1536 _ _ _ (by omega) (by omega) (by omega)
          ih.modulus hmi ih.rr ih.rr hv hv
      have hmod1 : Model.FastRepresents (mpMem 1536 1536 1536 (rrMem mpMem n mem i))
          0 n mm :=
        spec.mpFrame 1536 1536 1536 0 mm _ (by omega) (Or.inr (by omega)) ih.modulus
      have hr11 : Model.FastRepresents (mpMem 1536 1536 1536 (rrMem mpMem n mem i))
          1024 n (R % mm) :=
        spec.mpFrame 1536 1536 1536 1024 _ _ (by omega) (Or.inr (by omega)) ih.r1
      have hcc1 : Model.FastRepresents (mpMem 1536 1536 1536 (rrMem mpMem n mem i))
          1280 n (Limbs.radix * R % mm) :=
        spec.mpFrame 1536 1536 1536 1280 _ _ (by omega) (Or.inr (by omega)) ih.cc
      have hsel : Model.FastRepresents (mpMem 1536 1536 1536 (rrMem mpMem n mem i))
          (selOf n (5 - i)) n
          (if bitAt n (5 - i) = 0 then R % mm else Limbs.radix * R % mm) := by
        by_cases h0 : bitAt n (5 - i) = 0
        · rw [if_pos h0, selOf, h0]
          simpa using hr11
        · have h1 : bitAt n (5 - i) = 1 := by
            have := bitAt_le_one n (5 - i)
            omega
          rw [if_neg h0, selOf, h1]
          simpa using hcc1
      have hsellt : (if bitAt n (5 - i) = 0 then R % mm else Limbs.radix * R % mm)
          < mm := by
        by_cases h0 : bitAt n (5 - i) = 0
        · rw [if_pos h0]; exact Nat.mod_lt _ hm
        · rw [if_neg h0]; exact Nat.mod_lt _ hm
      show RrInv (rrStep mpMem n (5 - i) (rrMem mpMem n mem i)) n mm R
        (rrValue mm R n (i + 1))
      by_cases h0 : bitAt n (5 - i) = 0
      · rw [rrStep, if_pos h0, rrValue_succ, if_pos h0,
          montMul_by_one hm hcop (Model.montMul_lt hm _ _ _)]
        exact ⟨hmod1, hr11, hcc1, hsq⟩
      · have h1 : selOf n (5 - i) = 1280 := by
          have := bitAt_le_one n (5 - i); unfold selOf; omega
        rw [h1, if_neg h0] at hsel
        rw [if_neg h0] at hsellt
        rw [rrStep, if_neg h0, rrValue_succ, if_neg h0]
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact spec.mpFrame 1536 1280 1536 0 mm _ (by omega)
            (Or.inr (by omega)) hmod1
        · exact spec.mpFrame 1536 1280 1536 1024 _ _ (by omega)
            (Or.inr (by omega)) hr11
        · exact spec.mpFrame 1536 1280 1536 1280 _ _ (by omega)
            (Or.inr (by omega)) hcc1
        · exact spec.mpValue 1536 1280 1536 _ _ _ (by omega)
            (by omega) (by omega) hmod1 hmi1 hsq hsel
            (Model.montMul_lt hm _ _ _) hsellt

/-- **The `RR` chain postcondition, at the level of memory.**  After the six
iterations the `RR` block holds the Montgomery form of `radix ^ n`, which for
`R = radix ^ n mod m` is `R ^ 2 mod m`. -/
theorem rrMem_final {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn32 : n ≤ 8) (hcop : Nat.Coprime R mm) (mem : ByteArray)
    (hminv : MachineState.readWord mem 2720 = UInt256.ofNat minv)
    (hinv : RrInv mem n mm R (R % mm)) :
    Model.FastRepresents (rrMem mpMem n mem 6) 1536 n (rrValue mm R n 6) ∧
      rrValue mm R n 6 ≡ Limbs.radix ^ n * R [MOD mm] :=
  ⟨(rrMem_inv spec hm hcop hn32 mem hminv hinv 6).rr, rrValue_final hm hcop hn32⟩

/-! ### Bridges for the base-chain limb store

`Fast.Correct` needs to know that the word iteration `j` stores into `ONE` is
base limb `pb - 1 - j`, and that writing it replaces the whole `ONE` block. -/

/-- Reading one 32-byte word out of a longer big-endian field. -/
theorem bytesToNatPadded_word (bs : ByteArray) (off w r : Nat) (hr : r + 32 ≤ w) :
    Precompile.bytesToNatPadded bs off w / 256 ^ r % 256 ^ 32 =
      Precompile.bytesToNatPadded bs (off + (w - r - 32)) 32 := by
  have h1 := Challenge.EvmProof.Bytes.bytesToNatPadded_add bs off (w - r) r
  rw [show w - r + r = w from by omega] at h1
  have t1 := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow bs (off + (w - r)) r
  have h1' : Precompile.bytesToNatPadded bs off w =
      256 ^ r * Precompile.bytesToNatPadded bs off (w - r) +
        Precompile.bytesToNatPadded bs (off + (w - r)) r := by rw [h1]; ring
  have hdiv : Precompile.bytesToNatPadded bs off w / 256 ^ r =
      Precompile.bytesToNatPadded bs off (w - r) := by
    rw [h1', Nat.mul_add_div (pow_pos (by norm_num) r), Nat.div_eq_of_lt t1,
      Nat.add_zero]
  have h2 := Challenge.EvmProof.Bytes.bytesToNatPadded_add bs off (w - r - 32) 32
  rw [show w - r - 32 + 32 = w - r from by omega] at h2
  have t2 := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow bs
    (off + (w - r - 32)) 32
  have h2' : Precompile.bytesToNatPadded bs off (w - r) =
      Precompile.bytesToNatPadded bs (off + (w - r - 32)) 32 +
        Precompile.bytesToNatPadded bs off (w - r - 32) * 256 ^ 32 := by rw [h2]; ring
  rw [hdiv, h2', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt t2]

/-- The word iteration `j` stores into `ONE` is base limb `pb - 1 - j`. -/
theorem baseLimbWord_value (input : ByteArray) (bsize pb j : Nat)
    (hjpb : j < pb) (hle : 32 * (pb - j) ≤ bsize) :
    (baseLimbWord input bsize pb j).toNat =
      Precompile.bytesToNatPadded input 96 bsize / Limbs.radix ^ (pb - 1 - j) %
        Limbs.radix := by
  rw [baseLimbWord, Challenge.EvmProof.Bytes.readWord_toNat,
    show 96 + (bsize - 32 * (pb - j)) =
      96 + (bsize - 32 * (pb - j - 1) - 32) from by omega,
    ← bytesToNatPadded_word input 96 bsize (32 * (pb - j - 1)) (by omega),
    Limbs.pow_radix (pb - 1 - j), Limbs.radix_eq,
    show 32 * (pb - 1 - j) = 32 * (pb - j - 1) from by omega]

/-- Writing the least significant limb of a block whose value is below the
radix replaces the whole value. -/
theorem write_low_limb {mem : ByteArray} {n one : Nat} (word : UInt256)
    (hn : 0 < n) (hrep : Model.FastRepresents mem 768 n one)
    (hone : one < Limbs.radix) :
    Model.FastRepresents (storeWord mem (736 + 32 * n) word) 768 n word.toNat := by
  have h := Model.fastRepresents_write_limb (k := 0) (value' := word.toNat) word hrep hn
    (by
      rw [pow_zero, Nat.div_one, Nat.mod_eq_of_lt hone, Nat.mul_one, Nat.mul_one]
      omega)
  rw [show (768 : Nat) + 32 * (n - 1 - 0) = 736 + 32 * n from by omega] at h
  exact h


/-! ### The base chain, at the level of memory -/

theorem storeWord_frame (mem : ByteArray) (addr ptr count value : Nat) (w : UInt256)
    (hdisj : addr + 32 ≤ ptr ∨ ptr + 32 * count ≤ addr)
    (hrep : Model.FastRepresents mem ptr count value) :
    Model.FastRepresents (storeWord mem addr w) ptr count value :=
  Model.fastRepresents_writeWord_disjoint mem addr ptr count value w.toNat hdisj hrep

theorem storeWord_readWord_disjoint (mem : ByteArray) (addr a : Nat) (w : UInt256)
    (hdisj : a + 32 ≤ addr ∨ addr + 32 ≤ a) :
    MachineState.readWord (storeWord mem addr w) a =
      MachineState.readWord mem a := by
  refine Challenge.EvmProof.Memory.readWord_writeBytes_disjoint mem _ a addr ?_
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact hdisj

/-- A store below `V_S32` preserves the configuration words. -/
theorem frame_storeWord {mem : ByteArray} {n bsize minv addr : Nat} (w : UInt256)
    (haddr : addr + 32 ≤ 2688) (hf : Frame mem n bsize minv) :
    Frame (storeWord mem addr w) n bsize minv where
  s32 := by
    rw [storeWord_readWord_disjoint mem addr 2688 w (Or.inr (by omega))]; exact hf.s32
  minvW := by
    rw [storeWord_readWord_disjoint mem addr 2720 w (Or.inr (by omega))]
    exact hf.minvW
  ml := by
    rw [storeWord_readWord_disjoint mem addr 2752 w (Or.inr (by omega))]; exact hf.ml
  tl := by
    rw [storeWord_readWord_disjoint mem addr 2784 w (Or.inr (by omega))]; exact hf.tl
  eoff := by
    rw [storeWord_readWord_disjoint mem addr 2816 w (Or.inr (by omega))]
    exact hf.eoff

/-- An `MCOPY` below `V_S32` preserves the configuration words. -/
theorem frame_mcopyMem {mem : ByteArray} {n bsize minv dst src sz : Nat}
    (hfit : dst + sz ≤ 2688) (hf : Frame mem n bsize minv) :
    Frame (mcopyMem mem dst src sz) n bsize minv where
  s32 := by
    rw [readWord_mcopyMem_disjoint mem dst src sz 2688 (Or.inr (by omega))]
    exact hf.s32
  minvW := by
    rw [readWord_mcopyMem_disjoint mem dst src sz 2720 (Or.inr (by omega))]
    exact hf.minvW
  ml := by
    rw [readWord_mcopyMem_disjoint mem dst src sz 2752 (Or.inr (by omega))]
    exact hf.ml
  tl := by
    rw [readWord_mcopyMem_disjoint mem dst src sz 2784 (Or.inr (by omega))]
    exact hf.tl
  eoff := by
    rw [readWord_mcopyMem_disjoint mem dst src sz 2816 (Or.inr (by omega))]
    exact hf.eoff

theorem blValue_lt {mm b pb : Nat} (hm : 0 < mm) (t : Nat) :
    blValue mm b pb t < mm := by
  cases t with
  | zero => exact Nat.mod_lt _ hm
  | succ t => exact Nat.mod_lt _ hm


/-- The blocks the Horner loop reads and writes: the modulus, `ACC`, `ONE`
(whose value always fits in one limb), `CC` and `RR`. -/
structure BlInv (mem : ByteArray) (n mm R rr acc : Nat) : Prop where
  modulus : Model.FastRepresents mem 0 n mm
  accBlock : Model.FastRepresents mem 256 n acc
  oneBlock : ∃ one, one < Limbs.radix ∧ Model.FastRepresents mem 768 n one
  ccBlock : Model.FastRepresents mem 1280 n (Limbs.radix * R % mm)
  rrBlock : Model.FastRepresents mem 1536 n rr

/-- The memory one Horner iteration produces. -/
def blStepMem (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (input : ByteArray) (n bsize pb : Nat) (mem : ByteArray) (j : Nat) : ByteArray :=
  amMem 256 768 256
    (storeWord (mpMem 256 1280 256 mem) (736 + 32 * n)
      (baseLimbWord input bsize pb j))

theorem blMems_succ (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (input : ByteArray) (n bsize pb : Nat) (mem : ByteArray) (t : Nat) :
    blMems mpMem amMem input n bsize pb mem (t + 1) =
      blStepMem mpMem amMem input n bsize pb
        (blMems mpMem amMem input n bsize pb mem t) (t + 1) := rfl

/-- One Horner iteration: `ACC := MonPro(ACC, CC)`, store base limb
`pb - 1 - j` into `ONE`, `ACC := AddMod(ACC, ONE)`. -/
theorem blStep_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R rr minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hcop : Nat.Coprime R mm)
    (hradix : Limbs.radix ≤ mm) (input : ByteArray) (bsize pb j : Nat)
    (hjpb : j < pb) (hle : 32 * (pb - j) ≤ bsize)
    (mem : ByteArray) (acc : Nat) (hacc : acc < mm)
    (hminv : MachineState.readWord mem 2720 = UInt256.ofNat minv)
    (hinv : BlInv mem n mm R rr acc) :
    BlInv (blStepMem mpMem amMem input n bsize pb mem j) n mm R rr
      ((acc * Limbs.radix % mm +
        Precompile.bytesToNatPadded input 96 bsize / Limbs.radix ^ (pb - 1 - j) %
          Limbs.radix) % mm) := by
  obtain ⟨one, honelt, honerep⟩ := hinv.oneBlock
  -- the Montgomery multiply by `CC`
  have hmul := spec.mpValue 256 1280 256 mem acc (Limbs.radix * R % mm)
    (by omega) (by omega) (by omega) hinv.modulus hminv hinv.accBlock hinv.ccBlock
    hacc (Nat.mod_lt _ hm)
  rw [Model.montMul_const_form hm hcop (Nat.mod_modEq (Limbs.radix * R) mm) acc] at hmul
  have hmod1 := spec.mpFrame 256 1280 256 0 mm mem (by omega) (Or.inr (by omega))
    hinv.modulus
  have hone1 := spec.mpFrame 256 1280 256 768 one mem (by omega)
    (Or.inl (by omega)) honerep
  have hcc1 := spec.mpFrame 256 1280 256 1280 (Limbs.radix * R % mm) mem (by omega)
    (Or.inl (by omega)) hinv.ccBlock
  have hrr1 := spec.mpFrame 256 1280 256 1536 rr mem (by omega) (Or.inl (by omega))
    hinv.rrBlock
  -- the limb store into `ONE`
  have hstore := write_low_limb (baseLimbWord input bsize pb j) (by omega) hone1 honelt
  have hmod2 := storeWord_frame (mpMem 256 1280 256 mem) (736 + 32 * n) 0 n mm
    (baseLimbWord input bsize pb j) (Or.inr (by omega)) hmod1
  have hacc2 := storeWord_frame (mpMem 256 1280 256 mem) (736 + 32 * n) 256 n
    (acc * Limbs.radix % mm) (baseLimbWord input bsize pb j) (Or.inr (by omega)) hmul
  have hcc2 := storeWord_frame (mpMem 256 1280 256 mem) (736 + 32 * n) 1280 n
    (Limbs.radix * R % mm) (baseLimbWord input bsize pb j) (Or.inl (by omega)) hcc1
  have hrr2 := storeWord_frame (mpMem 256 1280 256 mem) (736 + 32 * n) 1536 n rr
    (baseLimbWord input bsize pb j) (Or.inl (by omega)) hrr1
  -- the modular addition
  have hlimb := baseLimbWord_value input bsize pb j hjpb hle
  have hlimblt : (baseLimbWord input bsize pb j).toNat < Limbs.radix :=
    (baseLimbWord input bsize pb j).val.isLt
  have hsum : acc * Limbs.radix % mm + (baseLimbWord input bsize pb j).toNat <
      2 * mm := by
    have h1 : acc * Limbs.radix % mm < mm := Nat.mod_lt _ hm
    omega
  have hadd := spec.amValue 256 768 256
    (storeWord (mpMem 256 1280 256 mem) (736 + 32 * n)
      (baseLimbWord input bsize pb j)) (acc * Limbs.radix % mm)
    (baseLimbWord input bsize pb j).toNat (by omega) (by omega) (by omega)
    hmod2 hacc2 hstore hsum
  rw [hlimb] at hadd
  refine ⟨?_, hadd, ⟨(baseLimbWord input bsize pb j).toNat, hlimblt, ?_⟩, ?_, ?_⟩
  · exact spec.amFrame 256 768 256 0 mm _ (by omega) (Or.inr (by omega)) hmod2
  · exact spec.amFrame 256 768 256 768 _ _ (by omega) (Or.inl (by omega))
      (hlimb ▸ hstore)
  · exact spec.amFrame 256 768 256 1280 (Limbs.radix * R % mm) _ (by omega)
      (Or.inl (by omega)) hcc2
  · exact spec.amFrame 256 768 256 1536 rr _ (by omega) (Or.inl (by omega)) hrr2

/-- `V_MINV` survives the Horner loop. -/
theorem readWord_blMems (mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (hmp : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (mpMem pa pb 256 mem') 2720 =
        MachineState.readWord mem' 2720)
    (ham : ∀ (pa pb : Nat) (mem' : ByteArray),
      MachineState.readWord (amMem pa pb 256 mem') 2720 =
        MachineState.readWord mem' 2720)
    (input : ByteArray) (n bsize pb : Nat) (hn32 : n ≤ 8) (mem : ByteArray)
    (t : Nat) :
    MachineState.readWord (blMems mpMem amMem input n bsize pb mem t) 2720 =
      MachineState.readWord mem 2720 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [blMems_succ, blStepMem, ham 256 768 _,
        storeWord_readWord_disjoint _ (736 + 32 * n) 2720 _ (Or.inr (by omega)),
        hmp 256 1280 _, ih]

/-- **The Horner loop, at the level of memory.** -/
theorem blMems_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R rr minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hcop : Nat.Coprime R mm)
    (hradix : Limbs.radix ≤ mm) (input : ByteArray) (bsize : Nat)
    (hb0 : 1 ≤ bsize) (mem : ByteArray)
    (hminv : MachineState.readWord mem 2720 = UInt256.ofNat minv)
    (hinv : BlInv mem n mm R rr
      (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) 0)) :
    ∀ t, t < pbOf bsize →
      BlInv (blMems mpMem amMem input n bsize (pbOf bsize) mem t) n mm R rr
        (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) t) := by
  intro t
  induction t with
  | zero => intro _; exact hinv
  | succ t ih =>
      intro ht
      have hstep := blStep_inv spec hm hn hn32 hcop hradix input bsize (pbOf bsize)
        (t + 1) ht (by unfold pbOf; omega)
        (blMems mpMem amMem input n bsize (pbOf bsize) mem t)
        (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) t)
        (blValue_lt hm t)
        ((readWord_blMems mpMem amMem
          (fun pa pb m => spec.mpMinv pa pb 256 m (by omega))
          (fun pa pb m => spec.amMinv pa pb 256 m (by omega)) input n bsize
          (pbOf bsize) hn32 mem t).trans hminv)
        (ih (by omega))
      rw [blMems_succ, blValue_succ]
      exact hstep

/-- **The base-chain postcondition, at the level of memory.**  After `pb - 1`
Horner iterations the `ACC` block holds `b mod m`. -/
theorem blMem_final {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R rr minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hcop : Nat.Coprime R mm)
    (hradix : Limbs.radix ≤ mm) (input : ByteArray) (bsize : Nat)
    (hb0 : 1 ≤ bsize) (mem : ByteArray)
    (hminv : MachineState.readWord mem 2720 = UInt256.ofNat minv)
    (hinv : BlInv mem n mm R rr
      (blValue mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize) 0)) :
    Model.FastRepresents
      (blMems mpMem amMem input n bsize (pbOf bsize) mem (pbOf bsize - 1)) 256 n
      (Precompile.bytesToNatPadded input 96 bsize % mm) := by
  have h := (blMems_inv spec hm hn hn32 hcop hradix input bsize hb0 mem hminv hinv
    (pbOf bsize - 1) (by unfold pbOf; omega)).accBlock
  rwa [blValue_final mm (Precompile.bytesToNatPadded input 96 bsize) (pbOf bsize)
    (by unfold pbOf; omega)] at h

/-- **`BASE := MonPro(ACC, RR)`.**  With `RR` holding `R ^ 2 mod m` this leaves
`b * R mod m` in the `BASE` block. -/
theorem blMem_base {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R rr b minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn32 : n ≤ 8) (hcop : Nat.Coprime R mm) (hrr : rr ≡ R * R [MOD mm])
    (hrrlt : rr < mm) (mem : ByteArray)
    (hminv : MachineState.readWord mem 2720 = UInt256.ofNat minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hacc : Model.FastRepresents mem 256 n (b % mm))
    (hrrb : Model.FastRepresents mem 1536 n rr) :
    Model.FastRepresents (mpMem 256 1536 512 mem) 512 n (b * R % mm) := by
  have h := spec.mpValue 256 1536 512 mem (b % mm) rr (by omega) (by omega)
    (by omega) hmod hminv hacc hrrb (Nat.mod_lt _ hm) hrrlt
  rwa [Model.montMul_const_form hm hcop hrr (b % mm),
    show b % mm * R % mm = b * R % mm from ((Nat.mod_modEq b mm).mul_right R)] at h


/-! ### The exponent loop, at the level of memory -/

/-- The bit the loop consumes at global step `t`: bit `7 - t % 8` of exponent
byte `t / 8`. -/
def expBits (input : ByteArray) (bsize : Nat) (t : Nat) : Nat :=
  bitAt (expByte input bsize (t / 8)) (7 - t % 8)

theorem expBits_eq (input : ByteArray) (bsize i j : Nat) (hj : j < 8) :
    expBits input bsize (8 * i + j) = bitAt (expByte input bsize i) (7 - j) := by
  unfold expBits
  rw [show (8 * i + j) / 8 = i from by omega, show (8 * i + j) % 8 = j from by omega]

theorem expAcc_lt {mm R bM : Nat} (hm : 0 < mm) (bits : Nat → Nat) (t : Nat) :
    expAcc mm R bM bits t < mm := by
  cases t with
  | zero => exact Nat.mod_lt _ hm
  | succ t =>
      rw [expAcc_succ]
      split
      · exact Model.montMul_lt hm _ _ _
      · exact Model.montMul_lt hm _ _ _

/-- The blocks the exponent loop reads and writes: the modulus, `ACC`, `BASE`
and `ONE` (untouched, and still one limb wide). -/
structure EbInv (mem : ByteArray) (n mm bM acc : Nat) : Prop where
  modulus : Model.FastRepresents mem 0 n mm
  accBlock : Model.FastRepresents mem 256 n acc
  baseBlock : Model.FastRepresents mem 512 n bM
  oneBlock : ∃ one, one < Limbs.radix ∧ Model.FastRepresents mem 768 n one

/-- One exponent bit: square `ACC`, and multiply by `BASE` when the bit is
set. -/
theorem bitStep_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn32 : n ≤ 8) (mem : ByteArray) (bM acc bit : Nat) (hbit : bit ≤ 1)
    (hbM : bM < mm) (hacc : acc < mm)
    (hminv : MachineState.readWord mem 2720 = UInt256.ofNat minv)
    (hinv : EbInv mem n mm bM acc) :
    EbInv (bitStep mpMem mem bit) n mm bM
      (if bit = 0 then Model.montMul mm R acc acc
        else Model.montMul mm R (Model.montMul mm R acc acc) bM) := by
  obtain ⟨one, honelt, honerep⟩ := hinv.oneBlock
  have hsq := spec.mpValue 256 256 256 mem acc acc (by omega) (by omega)
    (by omega) hinv.modulus hminv hinv.accBlock hinv.accBlock hacc hacc
  have hmod1 := spec.mpFrame 256 256 256 0 mm mem (by omega) (Or.inr (by omega))
    hinv.modulus
  have hbase1 := spec.mpFrame 256 256 256 512 bM mem (by omega)
    (Or.inl (by omega)) hinv.baseBlock
  have hone1 := spec.mpFrame 256 256 256 768 one mem (by omega)
    (Or.inl (by omega)) honerep
  rcases Nat.eq_zero_or_pos bit with h0 | hpos
  · subst h0
    refine ⟨hmod1, ?_, hbase1, ⟨one, honelt, hone1⟩⟩
    show Model.FastRepresents (mpMem 256 256 256 mem) 256 n
      (Model.montMul mm R acc acc)
    exact hsq
  · have h1 : bit = 1 := by omega
    subst h1
    have hmul := spec.mpValue 256 512 256 (mpMem 256 256 256 mem)
      (Model.montMul mm R acc acc) bM (by omega) (by omega) (by omega) hmod1
      ((spec.mpMinv 256 256 256 mem (by omega)).trans hminv) hsq hbase1
      (Model.montMul_lt hm _ _ _) hbM
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact spec.mpFrame 256 512 256 0 mm _ (by omega) (Or.inr (by omega)) hmod1
    · show Model.FastRepresents (mpMem 256 512 256 (mpMem 256 256 256 mem))
        256 n (Model.montMul mm R (Model.montMul mm R acc acc) bM)
      exact hmul
    · exact spec.mpFrame 256 512 256 512 bM _ (by omega) (Or.inl (by omega))
        hbase1
    · exact ⟨one, honelt, spec.mpFrame 256 512 256 768 one _ (by omega)
        (Or.inl (by omega)) hone1⟩


theorem bitAt_zero_of_lt {w r j : Nat} (hw : w < 2 ^ (r + 1)) (hj : r < j) :
    bitAt w j = 0 := by
  have hle : (2 : Nat) ^ (r + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold bitAt
  rw [Nat.div_eq_of_lt (by omega)]

theorem montMul_mont_one {mm R : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm) :
    Model.montMul mm R (R % mm) (R % mm) = R % mm :=
  Model.montMul_eq_of_modEq hm hcop
    (Nat.ModEq.mul_left (R % mm) (Nat.mod_modEq R mm).symm) (Nat.mod_lt _ hm)

/-- Squaring over leading zero bits leaves the accumulator at `Mont 1`. -/
theorem expAcc_of_zeros {mm R bM : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (bits : Nat → Nat) (k : Nat) (hz : ∀ j, j < k → bits j = 0) :
    expAcc mm R bM bits k = R % mm := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [expAcc_succ, hz k (by omega), if_pos rfl,
        ih (fun j hj => hz j (by omega))]
      exact montMul_mont_one hm hcop

/-- `Mont 1` is a left identity for Montgomery multiplication. -/
theorem montMul_one_left {mm R x : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hx : x < mm) : Model.montMul mm R (R % mm) x = x :=
  Model.montMul_eq_of_modEq hm hcop
    (by
      have h : (R % mm) * x ≡ R * x [MOD mm] :=
        Nat.ModEq.mul_right x (Nat.mod_modEq R mm)
      rw [Nat.mul_comm R x] at h
      exact h.symm) hx

/-- Leading zeros then the leading one: the accumulator lands exactly on the
Montgomery base. -/
theorem expAcc_of_zeros_then_one {mm R bM : Nat} (hm : 0 < mm)
    (hcop : Nat.Coprime R mm) (hbM : bM < mm) (bits : Nat → Nat) (k : Nat)
    (hz : ∀ j, j < k → bits j = 0) (hone : bits k ≠ 0) :
    expAcc mm R bM bits (k + 1) = bM := by
  rw [expAcc_succ, if_neg hone, expAcc_of_zeros hm hcop bits k hz,
    montMul_mont_one hm hcop, montMul_one_left hm hcop hbM]

/-- A nonzero byte has its leading bit set. -/
theorem bitAt_topExp {w : Nat} (hw : w < 256) (hne : w ≠ 0) :
    bitAt w (Lz.topExp w) = 1 := by
  obtain ⟨_, _, hlt⟩ := Lz.topBit_spec w hw
  have hle := Lz.topExp_le w hw hne
  have h1 : w / 2 ^ Lz.topExp w = 1 := by
    have hpos : 0 < (2 : Nat) ^ Lz.topExp w := by positivity
    have hge : 1 ≤ w / 2 ^ Lz.topExp w := (Nat.one_le_div_iff hpos).mpr hle
    have hlt2 : w / 2 ^ Lz.topExp w < 2 := by
      rw [Nat.div_lt_iff_lt_mul hpos]
      simpa [Nat.pow_succ, Nat.mul_comm] using hlt
    omega
  unfold bitAt
  rw [h1]

theorem bitMemsFrom_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn32 : n ≤ 8) (bM : Nat) (hbM : bM < mm) (w : Nat) (bits : Nat → Nat)
    (t0 j0 : Nat)
    (hbits : ∀ k, k < 8 - j0 → bits (t0 + j0 + k) = bitAt w (7 - (j0 + k)))
    (mem : ByteArray)
    (hminv : MachineState.readWord mem 2720 = UInt256.ofNat minv)
    (hinv : EbInv mem n mm bM (expAcc mm R bM bits (t0 + j0))) :
    ∀ k, k ≤ 8 - j0 →
      EbInv (bitMemsFrom mpMem w mem j0 k) n mm bM
        (expAcc mm R bM bits (t0 + j0 + k)) := by
  intro k
  induction k with
  | zero => intro _; exact hinv
  | succ k ih =>
      intro hk
      have hstep := bitStep_inv spec hm hn32 (bitMemsFrom mpMem w mem j0 k) bM
        (expAcc mm R bM bits (t0 + j0 + k)) (bitAt w (7 - (j0 + k)))
        (bitAt_le_one w (7 - (j0 + k))) hbM (expAcc_lt hm bits (t0 + j0 + k))
        ((readWord_bitMemsFrom mpMem 2720
          (fun pa pb m => spec.mpMinv pa pb 256 m (by omega)) w mem j0 k).trans hminv)
        (ih (by omega))
      rw [show t0 + j0 + (k + 1) = t0 + j0 + k + 1 from rfl, expAcc_succ,
        hbits k (by omega)]
      exact hstep


/-- The bits the loop skips are leading zeros of the exponent, so the
accumulator it starts from is the one the unskipped loop would have had. -/
theorem ebInv_shift {n mm R bM : Nat} (hm : 0 < mm)
    (hcop : Nat.Coprime R mm) (input : ByteArray) (bsize i : Nat)
    (mem : ByteArray)
    (hinv : EbInv mem n mm bM (expAcc mm R bM (expBits input bsize) (8 * i))) :
    EbInv mem n mm bM
      (expAcc mm R bM (expBits input bsize) (8 * i + lzSkip input bsize i)) := by
  by_cases h0 : i = 0
  · subst h0
    have hz : ∀ j, j < lzSkip input bsize 0 → expBits input bsize j = 0 := by
      intro j hj
      obtain ⟨_, hle7, hwlt⟩ := Lz.topBit_spec (expByte input bsize 0)
        ((YulSemantics.EVM.byteFrom input.toList (96 + bsize + 0)).toNat_lt)
      have hjs : j < 7 - Lz.topExp (expByte input bsize 0) := by
        simpa [lzSkip] using hj
      have hlt : j < 8 := by omega
      have heq := expBits_eq input bsize 0 j hlt
      rw [show 8 * 0 + j = j from by ring] at heq
      rw [heq]
      exact bitAt_zero_of_lt hwlt (by omega)
    have he : expAcc mm R bM (expBits input bsize)
        (8 * 0 + lzSkip input bsize 0) =
        expAcc mm R bM (expBits input bsize) 0 := by
      rw [show 8 * 0 + lzSkip input bsize 0 = lzSkip input bsize 0 from by ring,
        expAcc_of_zeros hm hcop _ _ hz]
      rfl
    rw [he]
    exact hinv
  · have hz0 : lzSkip input bsize i = 0 := by simp only [lzSkip, if_neg h0]
    rw [hz0, Nat.add_zero]
    exact hinv

/-- The accumulator the skipped first iteration would have produced.  The
leading bit of a nonzero byte is set, so that iteration squares `Mont(1)` — a
fixed point — and then multiplies by `BASE`, landing on `BASE`. -/
theorem expAcc_skipOne {mm R bM : Nat} (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hbM : bM < mm) (input : ByteArray) (bsize : Nat) (bits : Nat → Nat)
    (hwne : expByte input bsize 0 ≠ 0)
    (hbits : ∀ j, j < 8 → bits j = bitAt (expByte input bsize 0) (7 - j)) :
    expAcc mm R bM bits (lzSkip input bsize 0 + 1) = bM := by
  have hwlt : expByte input bsize 0 < 256 :=
    (YulSemantics.EVM.byteFrom input.toList (96 + bsize + 0)).toNat_lt
  have htop7 : Lz.topExp (expByte input bsize 0) ≤ 7 := (Lz.topBit_spec _ hwlt).2.1
  have hlz : lzSkip input bsize 0 = 7 - Lz.topExp (expByte input bsize 0) := by
    unfold lzSkip; rw [if_pos rfl]
  exact expAcc_of_zeros_then_one hm hcop hbM bits (lzSkip input bsize 0)
    (fun j hj => by
      rw [hbits j (by omega)]
      exact bitAt_gt_topExp hwlt (by omega))
    (by
      rw [hbits (lzSkip input bsize 0) (by omega),
        show 7 - lzSkip input bsize 0 = Lz.topExp (expByte input bsize 0)
          from by omega, bitAt_topExp hwlt hwne]
      exact one_ne_zero)

/-- `LZBASE` copies `BASE` onto `ACC`; every other named block is disjoint. -/
theorem ebInv_accCopy {mm bM n acc : Nat} (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (mem : ByteArray) (hinv : EbInv mem n mm bM acc) :
    EbInv (mcopyMem mem 256 512 (32 * n)) n mm bM bM where
  modulus := fastRepresents_mcopyMem_disjoint mem 256 512 (32 * n) 0 n mm
    (Or.inr (by omega)) hinv.modulus
  accBlock := fastRepresents_mcopyMem mem 256 512 n bM (by omega) hinv.baseBlock
  baseBlock := fastRepresents_mcopyMem_disjoint mem 256 512 (32 * n) 512 n bM
    (Or.inl (by omega)) hinv.baseBlock
  oneBlock := by
    obtain ⟨one, h1, h2⟩ := hinv.oneBlock
    exact ⟨one, h1, fastRepresents_mcopyMem_disjoint mem 256 512 (32 * n) 768 n
      one (Or.inl (by omega)) h2⟩

/-- **The exponent loop, at the level of memory.** -/
theorem ebMems_inv {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hcop : Nat.Coprime R mm) (hn : 2 ≤ n)
    (hn32 : n ≤ 8) (bM : Nat) (hbM : bM < mm) (input : ByteArray) (bsize : Nat)
    (mem : ByteArray)
    (hminv : MachineState.readWord mem 2720 = UInt256.ofNat minv)
    (hinv : EbInv mem n mm bM (expAcc mm R bM (expBits input bsize) 0)) :
    ∀ i, EbInv (ebMems mpMem input bsize n mem i) n mm bM
      (expAcc mm R bM (expBits input bsize) (8 * i)) := by
  intro i
  induction i with
  | zero => exact hinv
  | succ i ih =>
      have hwlt : expByte input bsize i < 256 :=
        (YulSemantics.EVM.byteFrom input.toList (96 + bsize + i)).toNat_lt
      have hj0 : lzSkip input bsize i ≤ 7 := lzSkip_le input bsize i
      have hminvI : MachineState.readWord (ebMems mpMem input bsize n mem i) 2720
          = UInt256.ofNat minv :=
        (readWord_ebMems mpMem 2720
          (fun pa pb m => spec.mpMinv pa pb 256 m (by omega)) input bsize n mem i
          (by omega) hn32).trans hminv
      show EbInv (byteMemAt mpMem input bsize n
        (ebMems mpMem input bsize n mem i) i) n mm bM _
      rw [byteMemAt]
      split
      · rename_i hc
        obtain ⟨rfl, hwne⟩ := hc
        have hj7 : lzSkip input bsize 0 ≤ 7 := lzSkip_le input bsize 0
        have hacc : expAcc mm R bM (expBits input bsize) (lzSkip input bsize 0 + 1)
            = bM :=
          expAcc_skipOne hm hcop hbM input bsize (expBits input bsize) hwne
            (fun j hj => by
              have h := expBits_eq input bsize 0 j hj
              rwa [Nat.mul_zero, Nat.zero_add] at h)
        have hminvC : MachineState.readWord
            (mcopyMem (ebMems mpMem input bsize n mem 0) 256 512 (32 * n)) 2720
            = UInt256.ofNat minv :=
          (readWord_mcopyMem_disjoint _ 256 512 (32 * n) 2720
            (Or.inr (by omega))).trans hminvI
        have hinvC : EbInv
            (mcopyMem (ebMems mpMem input bsize n mem 0) 256 512 (32 * n)) n mm bM
            (expAcc mm R bM (expBits input bsize)
              (0 + (lzSkip input bsize 0 + 1))) := by
          rw [Nat.zero_add, hacc]
          exact ebInv_accCopy hn hn32 _ ih
        have h := bitMemsFrom_inv spec hm hn32 bM hbM (expByte input bsize 0)
          (expBits input bsize) 0 (lzSkip input bsize 0 + 1)
          (fun k hk => by
            have hh := expBits_eq input bsize 0 (lzSkip input bsize 0 + 1 + k)
              (by omega)
            rw [Nat.mul_zero, Nat.zero_add] at hh
            rw [show 0 + (lzSkip input bsize 0 + 1) + k
              = lzSkip input bsize 0 + 1 + k from by omega]
            exact hh)
          (mcopyMem (ebMems mpMem input bsize n mem 0) 256 512 (32 * n))
          hminvC hinvC (7 - lzSkip input bsize 0) (by omega)
        rw [show 8 * (0 + 1)
          = 0 + (lzSkip input bsize 0 + 1) + (7 - lzSkip input bsize 0) from by omega]
        exact h
      · have hstart := ebInv_shift (n := n) (bM := bM) hm hcop input bsize i
          (ebMems mpMem input bsize n mem i) ih
        have h := bitMemsFrom_inv spec hm hn32 bM hbM (expByte input bsize i)
          (expBits input bsize) (8 * i) (lzSkip input bsize i)
          (fun k hk => by
            have := expBits_eq input bsize i (lzSkip input bsize i + k) (by omega)
            rwa [show 8 * i + (lzSkip input bsize i + k)
              = 8 * i + lzSkip input bsize i + k from by ring] at this)
          (ebMems mpMem input bsize n mem i) hminvI
          hstart (8 - lzSkip input bsize i) le_rfl
        rw [show 8 * (i + 1)
          = 8 * i + lzSkip input bsize i + (8 - lzSkip input bsize i) from by omega]
        exact h

/-- **The exponent-loop postcondition, at the level of memory.**  After the
`8 * esize` bits, `MSTORE ONE 1` and the closing `MonPro(ACC, ONE)`, the `ACC`
block holds the precompile's answer. -/
theorem ebMem_final {mpMem amMem : Nat → Nat → Nat → ByteArray → ByteArray}
    {n mm R bM b e minv : Nat} (spec : SubSpec mpMem amMem n mm R minv) (hm : 0 < mm)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hcop : Nat.Coprime R mm)
    (hradix : Limbs.radix ≤ mm) (hbM : bM < mm) (hbMform : bM ≡ b * R [MOD mm])
    (input : ByteArray) (bsize esize : Nat)
    (he : e = Precompile.bytesToNatPadded input (96 + bsize) esize)
    (mem : ByteArray)
    (hminv : MachineState.readWord mem 2720 = UInt256.ofNat minv)
    (hinv : EbInv mem n mm bM (expAcc mm R bM (expBits input bsize) 0)) :
    Model.FastRepresents
      (mpMem 256 768 256
        (storeWord (ebMems mpMem input bsize n mem esize) (736 + 32 * n)
          (UInt256.ofNat 1))) 256 n (Precompile.modPow b e mm) := by
  subst he
  have hmm1 : 1 < mm := lt_of_lt_of_le Limbs.radix_gt_one hradix
  have hloop := ebMems_inv spec hm hcop hn hn32 bM hbM input bsize mem hminv hinv esize
  have hmi : MachineState.readWord
      (storeWord (ebMems mpMem input bsize n mem esize) (736 + 32 * n)
        (UInt256.ofNat 1)) 2720 = UInt256.ofNat minv := by
    rw [storeWord_readWord_disjoint _ (736 + 32 * n) 2720 _ (Or.inr (by omega))]
    exact (readWord_ebMems mpMem 2720
      (fun pa pb m => spec.mpMinv pa pb 256 m (by omega)) input bsize n mem esize
      (by omega) hn32).trans hminv
  obtain ⟨one, honelt, honerep⟩ := hloop.oneBlock
  have hone := write_low_limb (UInt256.ofNat 1) (by omega) honerep honelt
  rw [show (UInt256.ofNat 1).toNat = 1 from by decide] at hone
  have hmod := storeWord_frame (ebMems mpMem input bsize n mem esize) (736 + 32 * n)
    0 n mm (UInt256.ofNat 1) (Or.inr (by omega)) hloop.modulus
  have hacc := storeWord_frame (ebMems mpMem input bsize n mem esize) (736 + 32 * n)
    256 n (expAcc mm R bM (expBits input bsize) (8 * esize)) (UInt256.ofNat 1)
    (Or.inr (by omega)) hloop.accBlock
  have hout := spec.mpValue 256 768 256
    (storeWord (ebMems mpMem input bsize n mem esize) (736 + 32 * n)
      (UInt256.ofNat 1))
    (expAcc mm R bM (expBits input bsize) (8 * esize)) 1 (by omega) (by omega)
    (by omega) hmod hmi hacc hone (expAcc_lt hm _ _) hmm1
  have helt : Precompile.bytesToNatPadded input (96 + bsize) esize <
      2 ^ (8 * esize) := by
    have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input (96 + bsize) esize
    rwa [show (256 : Nat) ^ esize = 2 ^ (8 * esize) from by
      rw [show (256 : Nat) = 2 ^ 8 from by norm_num, ← Nat.pow_mul]] at h
  have hbit : ∀ t, t < 8 * esize →
      expBits input bsize t =
        bitAt (Precompile.bytesToNatPadded input (96 + bsize) esize)
          (8 * esize - t - 1) := by
    intro t ht
    have hi : t / 8 < esize := by omega
    have h := bitAt_expByte input bsize esize (t / 8) (7 - t % 8) hi (by omega)
    rw [expBits, h, show 8 * (esize - 1 - t / 8) + (7 - t % 8) = 8 * esize - t - 1
      from by omega]
  rwa [expAcc_out hm hcop hbMform (expBits input bsize)
    (fun t => bitAt_le_one _ _) helt hbit] at hout

/-! ### The shape `Fast.Correct.FastPath.handled` consumes -/

theorem returnedState_isDone (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) (hstack : s.callStack = []) :
    (returnedState s mem n bsize esize msize).isDone = true := by
  simp [State.isDone, State.isHalted, State.isRunning, returnedState, hstack]

/-- **The halted state's result is the specification.**  Together with
`returnedState_isDone` and the chain traces this is exactly the
`∃ final, GasSteps … ∧ final.isDone = true ∧ final.toResult = .returned (spec input)`
that `Fast.Correct.FastPath.handled` asks for. -/
theorem returnedState_toResult (s : State) (mem input : ByteArray)
    (n bsize esize msize result : Nat) (hn : 2 ≤ n) (hm : msize ≤ 32 * n)
    (hmpos : 0 < msize)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hrep : Model.FastRepresents mem 256 n result)
    (hres : result = Precompile.modPow
      (Precompile.bytesToNatPadded input 96 bsize)
      (Precompile.bytesToNatPadded input (96 + bsize) esize)
      (Precompile.bytesToNatPadded input (96 + bsize + esize) msize)) :
    (returnedState s mem n bsize esize msize).toResult =
      .returned (Challenge.Modexp.spec input) := by
  rw [State.toResult_returned _ (by rfl),
    returned_eq_spec s mem input n bsize esize msize result hn hm hmpos hbsize hesize
      hmsz hrep hres]


/-! ### The shape `Fast.Correct.FastPath.handled` wants

`Challenge.EvmProof.GasSteps` is `Type`, not `Prop`, so the literal
`∃ final : State, GasSteps … final ∧ …` does not elaborate: `And` needs both
sides in `Prop`.  Wrapping the trace in `Nonempty` fixes that, and
`Classical.choice` recovers the trace on the other side.

This module deliberately does *not* import `Fast.Setup`: that import drags the
whole reference-proof closure (`Bytecode.Word`, `BigExponent`, `BigMul`, …)
into this file's dependency graph.  The final assembly therefore belongs in
`Fast.Correct`, which imports everything already; `handled_of_trace` is the
one-liner it needs. -/

/-- **The `handled` obligation, from a trace and the value of the `ACC` block.**
`entry` is the state the entry hop produces (`Main.trampolineState input 1362`),
`s` the carrier of the fast-path states (`initialState submissionBytecode input 0`,
whose `callStack` is `[]` by `rfl`). -/
theorem handled_of_trace (input : ByteArray) (entry s : State) (mem : ByteArray)
    (n bsize esize msize result : Nat)
    (hstack : s.callStack = [])
    (htrace : Challenge.EvmProof.GasSteps entry
      (returnedState s mem n bsize esize msize))
    (hn : 2 ≤ n) (hmsz32 : msize ≤ 32 * n) (hmpos : 0 < msize)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hrep : Model.FastRepresents mem 256 n result)
    (hres : result = Precompile.modPow
      (Precompile.bytesToNatPadded input 96 bsize)
      (Precompile.bytesToNatPadded input (96 + bsize) esize)
      (Precompile.bytesToNatPadded input (96 + bsize + esize) msize)) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps entry final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) :=
  ⟨returnedState s mem n bsize esize msize, ⟨htrace⟩,
    returnedState_isDone s mem n bsize esize msize hstack,
    returnedState_toResult s mem input n bsize esize msize result hn hmsz32 hmpos
      hbsize hesize hmsz hrep hres⟩


#print axioms blMem_final
#print axioms blMem_base
#print axioms ebMem_final
#print axioms rrMem_final
#print axioms returnedState_toResult
#print axioms handled_of_trace

/-! ## The gas traces of the three chains

These sit at the end of the module because each `iterateBounded` body needs the
value invariant at its own index, which the `*_inv` theorems above supply. -/

theorem jumpD (pc : Nat) (hpc : (UInt256.ofNat pc).toNat = pc)
    (hj : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode pc = true) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat pc).toNat = true := by
  rw [hpc]; exact hj


/-! ## The setup memory outside the modulus and `R1` blocks -/

/-- Nothing the setup block writes lands between `0x0400` and `0x1000`. -/
theorem readWord_setupMem_mid (input : ByteArray) (m0 target : Nat)
    (hm : Challenge.Modexp.modulusSize input ≤ 256)
    (hlo : 256 ≤ target) (hhi : target + 32 ≤ 1024) :
    MachineState.readWord (Setup.setupMem ByteArray.empty input m0) target =
      UInt256.ofNat 0 := by
  have hS := Setup.s32_le_256 input hm
  have hms := Setup.modulusSize_le_s32 input
  unfold Setup.setupMem Setup.modulusMem Setup.varsMem
  -- `setupMem` does not store the R1 seed, so this read-through peels one
  -- `mstoreAt` fewer before the two `writeBytes`.
  rw [Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_empty]

/-- `ACC`, `BASE` and the `ONE` slot are all zero when the setup hands over. -/
theorem fastSetup_zero_block (input : ByteArray) (hpath : Setup.FastPath input)
    (ptr : Nat) (hlo : 256 ≤ ptr) (hhi : ptr + 32 * Setup.limbs input ≤ 1024) :
    Model.FastRepresents (Setup.fastSetupMemory input) ptr (Setup.limbs input) 0 := by
  rw [Model.fastRepresents_zero_iff]
  intro j hj
  rw [Setup.fastSetupMemory,
    readWord_setupMem_mid input (Setup.lowLimb input) (ptr + 32 * j) hpath.2.1.2.2
      (by omega) (by omega),
    toNat_ofNat_self (by norm_num)]

/-- Nothing the setup block writes lands between `0x1020` and the variables. -/
theorem readWord_setupMem_high (input : ByteArray) (m0 target : Nat)
    (hm : Challenge.Modexp.modulusSize input ≤ 256)
    (hlo : 2048 ≤ target) (hhi : target + 32 ≤ 2688) :
    MachineState.readWord (Setup.setupMem ByteArray.empty input m0) target =
      UInt256.ofNat 0 := by
  have hS := Setup.s32_le_256 input hm
  have hms := Setup.modulusSize_le_s32 input
  unfold Setup.setupMem Setup.modulusMem Setup.varsMem
  -- There is no seed store, so the region starts at 0x1000 rather than
  -- 0x1020 and the `Or.inr` peel that stepped over it is no longer needed.
  rw [Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_writeBytes_ne _ _ _ _
      (Or.inr (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_mstoreAt_ne _ _ _ _ (Or.inl (by omega)),
    Setup.readWord_empty]

/-- The CIOS `t` block is still zero when the setup hands over, which is what
lets `CSUB` compute `radix ^ n - m` from `t[n] = 1` alone. -/
theorem fastSetup_tblock_zero (input : ByteArray) (hpath : Setup.FastPath input)
    (hn32 : Setup.limbs input ≤ 8) :
    Model.FastRepresents (Setup.fastSetupMemory input) 2112 (Setup.limbs input) 0 := by
  rw [Model.fastRepresents_zero_iff]
  intro j hj
  rw [Setup.fastSetupMemory,
    readWord_setupMem_high input (Setup.lowLimb input) (2112 + 32 * j) hpath.2.1.2.2
      (by omega) (by omega),
    toNat_ofNat_self (by norm_num)]

/-! ## The hand-over state, field by field -/

theorem fastSetup_code (input : ByteArray) :
    (Setup.fastSetupState input).executionEnv.code =
      Challenge.Modexp.submissionBytecode := rfl

theorem fastSetup_fork (input : ByteArray) :
    (Setup.fastSetupState input).fork = .Osaka := rfl

theorem fastSetup_halt (input : ByteArray) :
    (Setup.fastSetupState input).halt = .Running := rfl

theorem fastSetup_calldata (input : ByteArray) :
    (Setup.fastSetupState input).executionEnv.calldata = input := rfl

theorem fastSetup_callStack (input : ByteArray) :
    (Setup.fastSetupState input).callStack = [] := rfl

theorem fastSetup_notPrecompile (input : ByteArray) :
    Precompile.isPrecompileWithConfig
      (Setup.fastSetupState input).executionEnv.precompileConfig
      (Setup.fastSetupState input).executionEnv.fork
      (Setup.fastSetupState input).executionEnv.codeAddr = false :=
  Challenge.Modexp.deployAddress_not_precompile

/-- The setup block ends at the dispatcher entry (pc 2474, instruction index 2031)
with the plain outer frame, instead of at the Montgomery-form conversion call.
`Shift.dispState` is definitionally this state; it cannot be named here because
`ShiftStates` sits above this module.

Both numbers this comment and the term below used to carry -- pc 3374 and 2339 --
were pre-unroll and are not instruction starts in the 5,428-byte artifact
`fe8e9f61e6d3764a` at all: each lands inside a `PUSH` immediate.  Transcribed from
the decode rather than reconciled against each other: pc 2474 is a `JUMPDEST`
reached by the `PUSH2 0xcff; JUMP` at indices 2048..2049 and followed by
`DUP1; DUP4; EQ`, which is the dispatcher's compare chain.  `Fast.Setup` agrees
from two directions -- `fastSetupState_pc` is `UInt256.ofNat 2474` by `rfl`, and
its `jumpDest3296` certifies pc 2474 via `isValidJumpDest_index 2016`. -/
theorem fastSetup_entry_eq (input : ByteArray) :
    Setup.fastSetupState input =
      retTo (Setup.fastSetupState input) (Setup.fastSetupMemory input) (UInt256.ofNat 2474)
        (outer (Setup.limbs input) (Challenge.Modexp.baseSize input)
          (Challenge.Modexp.exponentSize input) (Challenge.Modexp.modulusSize input)) := rfl

/-! ## The top-level certificate -/

