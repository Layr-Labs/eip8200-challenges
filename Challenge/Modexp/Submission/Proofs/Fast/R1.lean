import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P15
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P17
import Challenge.EvmProof.Memory
import YulEvmCompiler.BytesLemmas
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The `R1B` guard of the appended Montgomery path

`R1B` occupies instruction indices 1768..1780 (pc 2901..2921).  It is entered
at pc 2901 with stack `[px, ret]`, exactly the calling convention of
`DOUBLE256`, and it dispatches:

* when the modulus's most significant bit is clear it jumps straight to
  `DOUBLE256` (pc 1911) with the stack and memory untouched, so that path is
  literally the old one;
* otherwise it stores `1` at `TN = 0x2020` and jumps to `CSUB` (pc 2642) with
  the same `[px, ret]` frame.

The second branch is the point.  `CSUB` computes `t[n] * radix ^ n + t_low`
reduced against `m`, and at this point in the setup the `t` block at
`TS = 0x2040` is still zero, so with `t[n] = 1` it computes `radix ^ n mod m`
— which is `R mod m`, the value the 256 modular doublings of `DOUBLE256`
produce.  Its side condition `t[n] * radix ^ n + t_low < 2 * m` is exactly the
top-bit guard: a modulus with its most significant bit set satisfies
`radix ^ n < 2 * m`, strictly because `m` is odd and `radix ^ n / 2` is not.

This module depends on `Fast.Csub` only through the value contract
`Csub.csub_correct`; the trace itself is spliced in by the caller.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R1

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero

/-! ## The guard -/

/-- The modulus's most significant limb has its top bit set.  This is the
decidable test the block performs with `MLOAD 0; PUSH1 255; SHR`. -/
def TopBitSet (mem : ByteArray) : Prop :=
  2 ^ 255 ≤ (MachineState.readWord mem 0).toNat

instance (mem : ByteArray) : Decidable (TopBitSet mem) := by
  unfold TopBitSet; infer_instance

/-- **The guard is exactly `CSUB`'s side condition.**  If the most significant
limb of an `n`-limb modulus has its top bit set then `radix ^ n < 2 * mm`.
The inequality is strict because `mm` is odd while `radix ^ n / 2` is a power
of two above one. -/
theorem radix_pow_lt_two_mul {mem : ByteArray} {n mm : Nat} (hn : 1 ≤ n)
    (hodd : mm % 2 = 1) (hmod : Model.FastRepresents mem 0 n mm)
    (htop : TopBitSet mem) :
    Limbs.radix ^ n < 2 * mm := by
  have htop' : 2 ^ 255 ≤ (MachineState.readWord mem 0).toNat := htop
  have hlimb : (MachineState.readWord mem 0).toNat =
      mm / Limbs.radix ^ (n - 1) % Limbs.radix := by
    simpa using Model.readWord_of_fastRepresents hmod (j := 0) (by omega)
  -- the modulus's top limb bounds `mm` from below, `% radix` only shrinks it
  have hge : 2 ^ 255 ≤ mm / Limbs.radix ^ (n - 1) :=
    le_trans (hlimb ▸ htop') (Nat.mod_le _ _)
  have hmul : 2 ^ 255 * Limbs.radix ^ (n - 1) ≤ mm :=
    le_trans (Nat.mul_le_mul_right _ hge) (Nat.div_mul_le_self _ _)
  have h2 : (2 : Nat) * 2 ^ 255 = Limbs.radix := by norm_num [Limbs.radix]
  have hhalf : 2 * (2 ^ 255 * Limbs.radix ^ (n - 1)) = Limbs.radix ^ n := by
    rw [← mul_assoc, h2, ← pow_succ']
    congr 1
    omega
  -- `radix ^ n / 2` is even and `mm` is odd, so the bound cannot be tight
  have heven : 2 ^ 255 * Limbs.radix ^ (n - 1) =
      2 * (2 ^ 254 * Limbs.radix ^ (n - 1)) := by
    rw [← mul_assoc]
    congr 1
  omega

/-- `t[n] := 1` at `TN = 0x2020`, the only memory the guard block writes. -/
def tnMem (mem : ByteArray) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded 1 32) 8224

/-! ## States at the block boundaries -/

/-- Subroutine entry, pc 2901, stack `[px, ret]`. -/
def entryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2901
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The fall-back target, pc 1911: `DOUBLE256`'s own entry, reached with the
stack and memory exactly as they arrived. -/
def dblState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1911
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- Between the test and the store, pc 2912. -/
def fastState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2912
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The `CSUB` entry, pc 2642, stack `[px, ret]`, with `t[n] = 1` stored.
`TN = 0x2020` lies below the `296` words the caller already holds, so the
store does not grow memory. -/
def csubState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2642
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := tnMem mem }

/-! ## Traces -/

/-- The test falls through when the modulus's top bit is set. -/
theorem run_test_fast (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat)
    (htop : TopBitSet mem) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1768
      (entryState s mem px ret rest) =
      some (fastState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hawL : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 0 32) = s.activeWords := by
    have : MachineState.activeWordsAfter s.activeWords.toNat 0 32 =
        s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
      exact Nat.max_eq_left (by omega)
    rw [this]
    exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have hshift : (UInt256.shiftRight (MachineState.readWord mem 0)
      (UInt256.ofNat 255)).toNat = 1 := by
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by omega)]
    have hlt : (MachineState.readWord mem 0).toNat < 2 ^ 256 :=
      (MachineState.readWord mem 0).val.isLt
    have := htop
    unfold TopBitSet at this
    simp only [Nat.shiftRight_eq_div_pow]
    omega
  have hcond : (UInt256.shiftRight (MachineState.readWord mem 0)
      (UInt256.ofNat 255)).isZero = UInt256.ofNat 0 := by
    simp only [UInt256.isZero, hshift]
    norm_num
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 }) [blk1768, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entryState, fastState, fastPC21, hc2, hc3, hc4, hrun, hcond, hfalse,
    hzeroNat, hawL,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

/-- The test jumps to the `R1C` guard otherwise. -/
theorem run_test_fallback (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat)
    (htop : ¬ TopBitSet mem) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1768
      (entryState s mem px ret rest) =
      some (guardEntryState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hawL : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 0 32) = s.activeWords := by
    have : MachineState.activeWordsAfter s.activeWords.toNat 0 32 =
        s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
      exact Nat.max_eq_left (by omega)
    rw [this]
    exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have hshift : (UInt256.shiftRight (MachineState.readWord mem 0)
      (UInt256.ofNat 255)).toNat = 0 := by
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by omega)]
    unfold TopBitSet at htop
    simp only [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by omega)
  have hcond : (UInt256.shiftRight (MachineState.readWord mem 0)
      (UInt256.ofNat 255)).isZero = UInt256.ofNat 1 := by
    simp only [UInt256.isZero, hshift]
    norm_num
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have h2995 : (2995 : UInt256) = UInt256.ofNat 2995 := by decide
  have h2995Nat : (UInt256.ofNat 2995).toNat = 2995 := by decide
  simp (config := { maxSteps := 400000 }) [blk1768, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entryState, guardEntryState, fastPC21, hc2, hc3, hc4, hcode, hrun, hcond, htrue,
    h2995, h2995Nat, jumpDest2995,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

/-- The store and the tail call into `CSUB`. -/
theorem run_fast (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1776
      (fastState s mem px ret rest) =
      some (csubState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have haw : MachineState.activeWordsAfter s.activeWords.toNat 8224 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
    exact Nat.max_eq_left (by omega)
  have haw' : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) =
      s.activeWords := by
    rw [haw]; exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  simp (config := { maxSteps := 400000 }) [blk1776, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fastState, csubState, tnMem, fastPC21, hc2, hc3, hc4, hcode, hrun,
    jumpDest2642, haw',
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

/-! ## The `R1C` small-top guard -/

/-- The two-limb small-top family: exactly two limbs, most significant limb
one, least significant limb below 256.  This is the decidable test the
`R1C` blocks perform against `V_S32` and the modulus block. -/
def SmallTop (n : Nat) (mem : ByteArray) : Prop :=
  n = 2 ∧ (MachineState.readWord mem 0).toNat = 1 ∧
    (MachineState.readWord mem 32).toNat < 256

instance (n : Nat) (mem : ByteArray) : Decidable (SmallTop n mem) := by
  unfold SmallTop; infer_instance

/-- `0` at `px` and `lo ^ 2` at `px + 32`: the only memory the `R1C` compute
block writes. -/
def smallMem (px : Nat) (mem : ByteArray) : ByteArray :=
  MachineState.writeBytes
    (MachineState.writeBytes mem
      (Data.Bytes.natToBytesPadded (0 : UInt256).toNat 32) px)
    (Data.Bytes.natToBytesPadded
      (MachineState.readWord mem 32 * MachineState.readWord mem 32).toNat 32)
    (px + 32)

/-- `R1C` guard entry, pc 2995, stack `[px, ret]`. -/
def guardEntryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2995
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- Between the size test and the top test, pc 3008. -/
def topState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3008
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- Between the top test and the low test, pc 3022. -/
def loState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3022
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- At the compute block, pc 3038. -/
def compEntryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3038
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- Back at the caller with `lo ^ 2` stored. -/
def smallDoneState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := ret
           stack := rest
           memory := smallMem px mem }

/-- Word multiplication in `toNat` form. -/
theorem word_toNat_mul (a b : UInt256) :
    (a * b).toNat = a.toNat * b.toNat % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

/-- **The modulus of the small-top family.** With two limbs and top limb one,
`mm = radix + lo`. -/
theorem smallTop_modulus {mem : ByteArray} {mm lo : Nat}
    (hmod : Model.FastRepresents mem 0 2 mm)
    (htop : (MachineState.readWord mem 0).toNat = 1)
    (hlo : (MachineState.readWord mem 32).toNat = lo) :
    mm = Limbs.radix + lo := by
  have hlimb0 : (MachineState.readWord mem (0 + 32 * 0)).toNat =
      mm / Limbs.radix ^ (2 - 1 - 0) % Limbs.radix :=
    Model.readWord_of_fastRepresents hmod (j := 0) (by decide)
  have hlimb1 : (MachineState.readWord mem (0 + 32 * 1)).toNat =
      mm / Limbs.radix ^ (2 - 1 - 1) % Limbs.radix :=
    Model.readWord_of_fastRepresents hmod (j := 1) (by decide)
  have hlimb0r : (MachineState.readWord mem 0).toNat =
      mm / Limbs.radix ^ (2 - 1) % Limbs.radix := by
    have h := hlimb0
    rwa [show (0 + 32 * 0) = 0 from rfl,
      show (2 - 1 - 0) = (2 - 1) from rfl] at h
  have hlimb1r : (MachineState.readWord mem 32).toNat =
      mm / Limbs.radix ^ (2 - 1 - 1) % Limbs.radix := by
    have h := hlimb1
    rwa [show (0 + 32 * 1) = 32 from rfl] at h
  have hnorm0 : mm / Limbs.radix ^ (2 - 1) % Limbs.radix =
      mm / Limbs.radix % Limbs.radix := by
    show mm / Limbs.radix ^ 1 % Limbs.radix = _
    rw [pow_one]
  have hnorm1 : mm / Limbs.radix ^ (2 - 1 - 1) % Limbs.radix =
      mm % Limbs.radix := by
    show mm / Limbs.radix ^ 0 % Limbs.radix = _
    rw [pow_zero, Nat.div_one]
  have hdiv1 : mm / Limbs.radix % Limbs.radix = 1 := by
    have h := hlimb0r.symm.trans htop
    rwa [hnorm0] at h
  have hmodEq : mm % Limbs.radix = lo := by
    have h := hlimb1r.symm.trans hlo
    rwa [hnorm1] at h
  have hltR : mm / Limbs.radix < Limbs.radix := by
    by_contra hcon
    push_neg at hcon
    have h1 : Limbs.radix * Limbs.radix ≤ mm / Limbs.radix * Limbs.radix :=
      Nat.mul_le_mul_right _ hcon
    have h2 : mm / Limbs.radix * Limbs.radix ≤ mm :=
      Nat.div_mul_le_self _ _
    have h3 : mm < Limbs.radix * Limbs.radix := by
      have h4 := hmod.1
      rwa [pow_two] at h4
    omega
  have hdiv : mm / Limbs.radix = 1 := by
    have h := hdiv1
    rwa [Nat.mod_eq_of_lt hltR] at h
  have h := Nat.div_add_mod' mm Limbs.radix
  rw [hdiv, hmodEq] at h
  omega

/-- `lo ^ 2` fits well below the radix for `lo < 256`. -/
theorem smallTop_sq_lt_radix {lo : Nat} (hlt : lo < 256) :
    lo ^ 2 < Limbs.radix := by
  have hRbig : (65536 : Nat) ≤ Limbs.radix := by decide
  have h65 : (256 : Nat) * 256 = 65536 := by decide
  rw [pow_two]
  by_cases hlo0 : lo = 0
  · subst hlo0
    simp only [Nat.mul_zero]
    omega
  · have hpos : 0 < lo := Nat.pos_of_ne_zero hlo0
    have s1 : lo * lo < lo * 256 :=
      Nat.mul_lt_mul_of_pos_left hlt hpos
    have s2 : lo * 256 < 256 * 256 :=
      Nat.mul_lt_mul_of_pos_right hlt (by decide)
    omega

/-- `lo ^ 2` fits well below any small-top modulus. -/
theorem smallTop_sq_lt_mm {mm lo : Nat} (hmm : mm = Limbs.radix + lo)
    (hlt : lo < 256) : lo ^ 2 < mm :=
  lt_of_lt_of_le (smallTop_sq_lt_radix hlt) (by omega)

/-- **`R mod m` for the small-top family.** With two limbs, top limb one and
low limb `lo < 256`, `radix ^ 2 % mm = lo ^ 2`. -/
theorem radix_sq_mod_small {mem : ByteArray} {mm lo : Nat}
    (hmod : Model.FastRepresents mem 0 2 mm)
    (htop : (MachineState.readWord mem 0).toNat = 1)
    (hlo : (MachineState.readWord mem 32).toNat = lo)
    (hlt : lo < 256) :
    Limbs.radix ^ 2 % mm = lo ^ 2 := by
  have hmm := smallTop_modulus hmod htop hlo
  have h256 : (256 : Nat) ≤ Limbs.radix := by decide
  have hM : mm - 2 * lo = Limbs.radix - lo := by omega
  have hD : lo + (Limbs.radix - lo) = Limbs.radix :=
    Nat.add_sub_cancel' (by omega)
  have eR : Limbs.radix * Limbs.radix
      = Limbs.radix * (Limbs.radix - lo) + Limbs.radix * lo := by
    have hmul := Nat.mul_add Limbs.radix lo (Limbs.radix - lo)
    rw [hD] at hmul
    omega
  have eL : Limbs.radix * lo = lo * lo + lo * (Limbs.radix - lo) := by
    have hmul := Nat.mul_add lo lo (Limbs.radix - lo)
    rw [hD] at hmul
    have hcomm : lo * Limbs.radix = Limbs.radix * lo := Nat.mul_comm _ _
    omega
  have hdecomp : Limbs.radix ^ 2 = lo ^ 2 + (mm - 2 * lo) * mm := by
    rw [hM, hmm, pow_two]
    have e1 : (Limbs.radix - lo) * (Limbs.radix + lo)
        = Limbs.radix * (Limbs.radix - lo) + lo * (Limbs.radix - lo) := by
      have hm := Nat.mul_add (Limbs.radix - lo) Limbs.radix lo
      rwa [Nat.mul_comm (Limbs.radix - lo) Limbs.radix,
        Nat.mul_comm (Limbs.radix - lo) lo] at hm
    rw [e1]
    omega
  have hltmm : lo ^ 2 < mm := smallTop_sq_lt_mm hmm hlt
  rw [hdecomp, Nat.mul_comm (mm - 2 * lo) mm, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hltmm]

/-- Reading back the high limb the compute block wrote. -/
theorem readWord_smallMem_high (mem : ByteArray) (px : Nat) :
    MachineState.readWord (smallMem px mem) px = (0 : UInt256) := by
  simp only [smallMem]
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
    (Or.inl le_rfl)]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

/-- Reading back the low limb the compute block wrote. -/
theorem readWord_smallMem_low (mem : ByteArray) (px : Nat) :
    MachineState.readWord (smallMem px mem) (px + 32) =
      MachineState.readWord mem 32 * MachineState.readWord mem 32 := by
  simp only [smallMem]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

/-- Blocks at or above `px + 64` survive the compute block. -/
theorem readWord_smallMem_high_addr (mem : ByteArray) (px : Nat) (addr : Nat)
    (haddr : px + 64 ≤ addr) :
    MachineState.readWord (smallMem px mem) addr =
      MachineState.readWord mem addr := by
  simp only [smallMem]
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
    (Or.inr (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega))]
  exact Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
    (Or.inr (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega))

/-- **The compute block leaves `R mod m` at `R1`.** -/
theorem smallMem_represents {mem : ByteArray} {mm lo : Nat}
    (hmod : Model.FastRepresents mem 0 2 mm)
    (htop : (MachineState.readWord mem 0).toNat = 1)
    (hlo : (MachineState.readWord mem 32).toNat = lo)
    (hlt : lo < 256) :
    Model.FastRepresents (smallMem 4096 mem) 4096 2 (Limbs.radix ^ 2 % mm) := by
  have hval : Limbs.radix ^ 2 % mm = lo ^ 2 :=
    radix_sq_mod_small hmod htop hlo hlt
  have hmm := smallTop_modulus hmod htop hlo
  have h0 : ((0 : UInt256)).toNat = 0 := by decide
  have hltR : lo ^ 2 < Limbs.radix := smallTop_sq_lt_radix hlt
  have hltmm : lo ^ 2 < mm := smallTop_sq_lt_mm hmm hlt
  have hlt2 : lo ^ 2 < Limbs.radix ^ 2 := lt_trans hltmm hmod.1
  have hww : (MachineState.readWord mem 32 * MachineState.readWord mem 32).toNat =
      lo ^ 2 % Limbs.radix := by
    have hmul : (MachineState.readWord mem 32 * MachineState.readWord mem 32).toNat
        = (MachineState.readWord mem 32).toNat * (MachineState.readWord mem 32).toNat %
          Limbs.radix :=
      word_toNat_mul _ _
    rw [hlo] at hmul
    have hsq : lo * lo = lo ^ 2 := (pow_two lo).symm
    rwa [hsq] at hmul
  refine Model.fastRepresents_of_limbs ?_ ?_
  · rw [hval]; exact hlt2
  · intro k hk
    have hk0 : 0 ≤ k := by omega
    interval_cases k
    · have ha : (4096 : Nat) + 32 * (2 - 1 - 0) = 4128 := by decide
      rw [ha, hval, pow_zero, Nat.div_one]
      have h4128 : MachineState.readWord (smallMem 4096 mem) 4128 =
          MachineState.readWord mem 32 * MachineState.readWord mem 32 :=
        readWord_smallMem_low mem 4096
      rw [h4128]
      exact hww
    · have ha : (4096 : Nat) + 32 * (2 - 1 - 1) = 4096 := by decide
      rw [ha, hval, pow_one, readWord_smallMem_high]
      have hdiv0 : lo ^ 2 / Limbs.radix = 0 := Nat.div_eq_of_lt hltR
      rw [h0, hdiv0, Nat.mod_eq_of_lt Limbs.radix_pos]

/-! ## Traces through the `R1C` blocks -/

set_option linter.unusedSimpArgs false in
/-- The size test falls through when the frame holds two limbs. -/
theorem run_g0_pass (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat 64) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1823
      (guardEntryState s mem px ret rest) =
      some (topState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have haw : MachineState.activeWordsAfter s.activeWords.toNat 9344 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
    exact Nat.max_eq_left (by omega)
  have haw' : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) =
      s.activeWords := by
    rw [haw]; exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have h9344 : (9344 : UInt256) = UInt256.ofNat 9344 := by decide
  have h9344mod : 9344 % 2 ^ 256 = 9344 := by decide
  have h64 : (64 : UInt256) = UInt256.ofNat 64 := by decide
  have heq : UInt256.eq (UInt256.ofNat 64) (UInt256.ofNat 64) =
      UInt256.ofNat 1 := by decide
  have hcond : (UInt256.ofNat 1).isZero = UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 }) [blk1823, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    guardEntryState, topState, fastPC23, hc2, hc3, hc4, hrun,
    hs32, haw', h9344, h9344mod, h64, heq, hcond, hfalse,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
/-- The size test jumps back to `DOUBLE256` otherwise. -/
theorem run_g0_bail (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat)
    (hs32ne : MachineState.readWord mem 9344 ≠ UInt256.ofNat 64) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1823
      (guardEntryState s mem px ret rest) =
      some (dblState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have haw : MachineState.activeWordsAfter s.activeWords.toNat 9344 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
    exact Nat.max_eq_left (by omega)
  have haw' : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) =
      s.activeWords := by
    rw [haw]; exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have h9344 : (9344 : UInt256) = UInt256.ofNat 9344 := by decide
  have h9344mod : 9344 % 2 ^ 256 = 9344 := by decide
  have h64 : (64 : UInt256) = UInt256.ofNat 64 := by decide
  have h64mod : 64 % 2 ^ 256 = 64 := by decide
  have heq : UInt256.eq (UInt256.ofNat 64) (MachineState.readWord mem 9344) =
      UInt256.ofNat 0 := by
    rw [UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat, h64mod]
    apply if_neg
    intro hcon
    apply hs32ne
    rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat, ← hcon]
  have hcond : (UInt256.ofNat 0).isZero = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have h1911 : (1911 : UInt256) = UInt256.ofNat 1911 := by decide
  have h1911Nat : (UInt256.ofNat 1911).toNat = 1911 := by decide
  simp (config := { maxSteps := 400000 }) [blk1823, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    guardEntryState, dblState, fastPC23, hc2, hc3, hc4, hcode, hrun,
    hs32ne, haw', h9344, h9344mod, h64, heq, hcond, htrue,
    h1911, h1911Nat, jumpDest1911,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
/-- The top test is taken when the most significant limb is one. -/
theorem run_g1_pass (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat)
    (htop1 : (MachineState.readWord mem 0).toNat = 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1831pass
      (topState s mem px ret rest) =
      some (loState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hawL : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 0 32) = s.activeWords := by
    have : MachineState.activeWordsAfter s.activeWords.toNat 0 32 =
        s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
      exact Nat.max_eq_left (by omega)
    rw [this]
    exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h1mod : 1 % 2 ^ 256 = 1 := by decide
  have heq : UInt256.eq (UInt256.ofNat 1) (MachineState.readWord mem 0) =
      UInt256.ofNat 1 := by
    rw [UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat, h1mod, htop1]
    exact if_pos rfl
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have h3022 : (3022 : UInt256) = UInt256.ofNat 3022 := by decide
  have h3022Nat : (UInt256.ofNat 3022).toNat = 3022 := by decide
  simp (config := { maxSteps := 400000 }) [blk1831pass, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    topState, loState, fastPC23, hc2, hc3, hc4, hcode, hrun,
    htop1, hawL, hzeroNat, h1, heq, htrue,
    h3022, h3022Nat, jumpDest3022,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
/-- The top test jumps back to `DOUBLE256` otherwise. -/
theorem run_g1_bail (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat)
    (htopne : MachineState.readWord mem 0 ≠ UInt256.ofNat 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1831bail
      (topState s mem px ret rest) =
      some (dblState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hawL : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 0 32) = s.activeWords := by
    have : MachineState.activeWordsAfter s.activeWords.toNat 0 32 =
        s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
      exact Nat.max_eq_left (by omega)
    rw [this]
    exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h1mod : 1 % 2 ^ 256 = 1 := by decide
  have heq : UInt256.eq (UInt256.ofNat 1) (MachineState.readWord mem 0) =
      UInt256.ofNat 0 := by
    rw [UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat, h1mod]
    apply if_neg
    intro hcon
    apply htopne
    rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat, ← hcon]
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have h1911 : (1911 : UInt256) = UInt256.ofNat 1911 := by decide
  have h1911Nat : (UInt256.ofNat 1911).toNat = 1911 := by decide
  simp (config := { maxSteps := 400000 }) [blk1831bail, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    topState, dblState, fastPC23, hc2, hc3, hc4, hcode, hrun,
    htopne, hawL, hzeroNat, h1, heq, hfalse,
    h1911, h1911Nat, jumpDest1911,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
/-- The low test is taken when the least significant limb is below 256. -/
theorem run_g2_pass (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat)
    (hlo256 : (MachineState.readWord mem 32).toNat < 256) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1840pass
      (loState s mem px ret rest) =
      some (compEntryState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have haw : MachineState.activeWordsAfter s.activeWords.toNat 32 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
    exact Nat.max_eq_left (by omega)
  have haw' : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 32 32) =
      s.activeWords := by
    rw [haw]; exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h32mod : 32 % 2 ^ 256 = 32 := by decide
  have h256 : (256 : UInt256) = UInt256.ofNat 256 := by decide
  have h256mod : 256 % 2 ^ 256 = 256 := by decide
  have hgt : UInt256.gt (UInt256.ofNat 256) (MachineState.readWord mem 32) =
      UInt256.ofNat 1 := by
    rw [UInt256.gt, Challenge.EvmProof.Word.word_toNat_ofNat, h256mod]
    exact if_pos hlo256
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have h3038 : (3038 : UInt256) = UInt256.ofNat 3038 := by decide
  have h3038Nat : (UInt256.ofNat 3038).toNat = 3038 := by decide
  simp (config := { maxSteps := 400000 }) [blk1840pass, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loState, compEntryState, fastPC23, hc2, hc3, hc4, hcode, hrun,
    hlo256, haw', h32, h32mod, h256, hgt, htrue,
    h3038, h3038Nat, jumpDest3038,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
/-- The low test jumps back to `DOUBLE256` otherwise. -/
theorem run_g2_bail (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat)
    (hlo256n : (256 : Nat) ≤ (MachineState.readWord mem 32).toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1840bail
      (loState s mem px ret rest) =
      some (dblState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have haw : MachineState.activeWordsAfter s.activeWords.toNat 32 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
    exact Nat.max_eq_left (by omega)
  have haw' : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 32 32) =
      s.activeWords := by
    rw [haw]; exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h32mod : 32 % 2 ^ 256 = 32 := by decide
  have h256 : (256 : UInt256) = UInt256.ofNat 256 := by decide
  have h256mod : 256 % 2 ^ 256 = 256 := by decide
  have hgt : UInt256.gt (UInt256.ofNat 256) (MachineState.readWord mem 32) =
      UInt256.ofNat 0 := by
    rw [UInt256.gt, Challenge.EvmProof.Word.word_toNat_ofNat, h256mod]
    apply if_neg
    omega
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  have h1911 : (1911 : UInt256) = UInt256.ofNat 1911 := by decide
  have h1911Nat : (UInt256.ofNat 1911).toNat = 1911 := by decide
  simp (config := { maxSteps := 400000 }) [blk1840bail, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loState, dblState, fastPC23, hc2, hc3, hc4, hcode, hrun,
    hlo256n, haw', h32, h32mod, h256, hgt, hfalse,
    h1911, h1911Nat, jumpDest1911,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
/-- The compute block stores `lo ^ 2` and returns. -/
theorem run_compute (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) (hact : 296 ≤ s.activeWords.toNat)
    (hpx256 : px < 2 ^ 256) (hpx32 : px + 32 < 2 ^ 256)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      ret.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1849
      (compEntryState s mem px ret rest) =
      some (smallDoneState s mem px ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have haw0 : MachineState.activeWordsAfter s.activeWords.toNat 32 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
    exact Nat.max_eq_left (by omega)
  have haw0' : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 32 32) =
      s.activeWords := by
    rw [haw0]; exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have haw1 : MachineState.activeWordsAfter s.activeWords.toNat 4096 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
    exact Nat.max_eq_left (by omega)
  have haw1' : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 4096 32) =
      s.activeWords := by
    rw [haw1]; exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have haw2 : MachineState.activeWordsAfter s.activeWords.toNat 4128 32 =
      s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : ¬(32 = 0))]
    exact Nat.max_eq_left (by omega)
  have haw2' : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 4128 32) =
      s.activeWords := by
    rw [haw2]; exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h32mod : 32 % 2 ^ 256 = 32 := by decide
  have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have hpxmod : px % 2 ^ 256 = px := Nat.mod_eq_of_lt hpx256
  have hpx32mod : (px + 32) % 2 ^ 256 = px + 32 := Nat.mod_eq_of_lt hpx32
  have hadd : UInt256.ofNat 32 + UInt256.ofNat px = UInt256.ofNat (px + 32) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact Challenge.EvmProof.Word.ofNat_add_ofNat hpx32
  simp (config := { maxSteps := 400000 }) [blk1849, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    compEntryState, smallDoneState, smallMem, fastPC23,
    hc2, hc3, hc4, hc5, hc6, hcode, hrun, hjump,
    haw0', haw1, haw1', haw2', h32, h32mod, h0, hpxmod, hpx32mod, hadd, hpx256, hpx32,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt, List.exchange,
    State.activeWordsAfterUInt256]

end Challenge.Modexp.Submission.Proofs.Fast.R1
