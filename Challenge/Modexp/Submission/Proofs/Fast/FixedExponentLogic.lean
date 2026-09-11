import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Arithmetic and memory invariant for the fixed-exponent square chain

This module isolates the artifact-independent part of the fixed-exponent
shortcut.  Concrete dispatcher and located-instruction proofs belong in later
modules, so regenerating bytecode PCs does not invalidate this kernel proof.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedExponentLogic

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs

/-- Repeated in-place Montgomery squaring after BASE has been copied to ACC. -/
def squareMems (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | t + 1 => mpMem 256 256 256 (squareMems mpMem mem t)

/-- Arithmetic counterpart of `squareMems`. -/
def squareValue (mm R acc : Nat) : Nat → Nat
  | 0 => acc
  | t + 1 => Model.montMul mm R
      (squareValue mm R acc t) (squareValue mm R acc t)

/-- Copy BASE to ACC and then perform `t` Montgomery squares. -/
def fixedMems (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (n : Nat) (mem : ByteArray) : Nat → ByteArray
  | 0 => Exp.mcopyMem mem 256 512 (32 * n)
  | t + 1 => mpMem 256 256 256 (fixedMems mpMem n mem t)

/-- Value represented by ACC after `t` fixed-chain squares. -/
def fixedValue (mm R bM : Nat) : Nat → Nat
  | 0 => bM
  | t + 1 => Model.montMul mm R
      (fixedValue mm R bM t) (fixedValue mm R bM t)

theorem fixedMems_eq_squareMems
    (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (n : Nat) (mem : ByteArray) (t : Nat) :
    fixedMems mpMem n mem t =
      squareMems mpMem (Exp.mcopyMem mem 256 512 (32 * n)) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [fixedMems, squareMems, ih]

theorem fixedValue_eq_squareValue (mm R bM t : Nat) :
    fixedValue mm R bM t = squareValue mm R bM t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [fixedValue, squareValue, ih]

theorem fixedValue_lt {mm R bM : Nat} (hm : 0 < mm) (hbM : bM < mm) :
    ∀ t, fixedValue mm R bM t < mm := by
  intro t
  induction t with
  | zero => exact hbM
  | succ t _ => exact Model.montMul_lt hm _ _ _

theorem fixedValue_form {mm R b bM : Nat} (hm : 0 < mm)
    (hcop : Nat.Coprime R mm) (hbMform : bM ≡ b * R [MOD mm]) :
    ∀ t, fixedValue mm R bM t ≡ b ^ (2 ^ t) * R [MOD mm] := by
  intro t
  induction t with
  | zero => simpa [fixedValue] using hbMform
  | succ t ih =>
      rw [fixedValue]
      have hs := Model.mont_sq_step hm hcop ih
      rw [hs, pow_succ, Nat.mul_comm (2 ^ t) 2]
      exact Nat.mod_modEq _ _

theorem squareValue_lt {mm R acc : Nat} (hm : 0 < mm) (hacc : acc < mm) :
    ∀ t, squareValue mm R acc t < mm := by
  intro t
  induction t with
  | zero => exact hacc
  | succ t _ => exact Model.montMul_lt hm _ _ _

theorem squareMems_step_add
    (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (mem : ByteArray) (t : Nat) :
    squareMems mpMem (mpMem 256 256 256 mem) t =
      squareMems mpMem mem (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [squareMems, ih]

theorem squareValue_step_add (mm R acc t : Nat) :
    squareValue mm R (Model.montMul mm R acc acc) t =
      squareValue mm R acc (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [squareValue, ih]

theorem fixedMems_frame {s : State} {n bsize mm minv : Nat}
    (sub : Exp.Subroutines s n bsize mm minv) (mem : ByteArray)
    (hn32 : n ≤ 8)
    (hframe : Exp.Frame mem n bsize minv) :
    ∀ t, Exp.Frame (fixedMems sub.mpMem n mem t) n bsize minv := by
  intro t
  induction t with
  | zero => exact Exp.frame_mcopyMem (by omega) hframe
  | succ t ih => exact sub.mpFrame 256 256 256 _ (by omega) ih

theorem squareMems_frame {s : State} {n bsize mm minv : Nat}
    (sub : Exp.Subroutines s n bsize mm minv) (mem : ByteArray)
    (hframe : Exp.Frame mem n bsize minv) :
    ∀ t, Exp.Frame (squareMems sub.mpMem mem t) n bsize minv := by
  intro t
  induction t with
  | zero => exact hframe
  | succ t ih => exact sub.mpFrame 256 256 256 _ (by omega) ih

theorem squareMems_inv {s : State} {n bsize mm minv R bM acc : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (hm : 0 < mm) (hn32 : n ≤ 8) (hacc : acc < mm)
    (hframe : Exp.Frame mem n bsize minv)
    (hinv : Exp.EbInv mem n mm bM acc) :
    ∀ t, Exp.EbInv (squareMems sub.mpMem mem t) n mm bM
      (squareValue mm R acc t) := by
  intro t
  induction t with
  | zero => exact hinv
  | succ t ih =>
      have hf := squareMems_frame sub mem hframe t
      obtain ⟨one, honeLt, honeRep⟩ := ih.oneBlock
      refine ⟨?_, ?_, ?_, ⟨one, honeLt, ?_⟩⟩
      · exact spec.mpFrame 256 256 256 0 mm _ (by omega)
          (Or.inr (by omega)) ih.modulus
      · exact spec.mpValue 256 256 256 _ _ _
          (by omega) (by omega) (by omega) ih.modulus hf.minvW
          ih.accBlock ih.accBlock (squareValue_lt hm hacc t)
          (squareValue_lt hm hacc t)
      · exact spec.mpFrame 256 256 256 512 bM _ (by omega)
          (Or.inl (by omega)) ih.baseBlock
      · exact spec.mpFrame 256 256 256 768 one _ (by omega)
          (Or.inl (by omega)) honeRep

/-- The initial BASE-to-ACC copy and every later square preserve the four
named Montgomery blocks. -/
theorem fixedMems_inv {s : State} {n bsize mm minv R bM : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (hm : 0 < mm) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hbM : bM < mm)
    (hframe : Exp.Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hbase : Model.FastRepresents mem 512 n bM)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents mem 768 n one) :
    ∀ t, Exp.EbInv (fixedMems sub.mpMem n mem t) n mm bM
      (fixedValue mm R bM t) := by
  intro t
  induction t with
  | zero =>
      refine ⟨?_, Exp.fastRepresents_mcopyMem mem 256 512 n bM
        (by omega) hbase, ?_, ?_⟩
      · exact Exp.fastRepresents_mcopyMem_disjoint mem 256 512 (32 * n)
          0 n mm (Or.inr (by omega)) hmod
      · exact Exp.fastRepresents_mcopyMem_disjoint mem 256 512 (32 * n)
          512 n bM (Or.inl (by omega)) hbase
      · obtain ⟨one, honeLt, honeRep⟩ := hone
        exact ⟨one, honeLt, Exp.fastRepresents_mcopyMem_disjoint mem 256 512
          (32 * n) 768 n one (Or.inl (by omega)) honeRep⟩
  | succ t ih =>
      have hf : Exp.Frame (fixedMems sub.mpMem n mem t) n bsize minv :=
        fixedMems_frame sub mem hn32 hframe t
      obtain ⟨one, honeLt, honeRep⟩ := ih.oneBlock
      refine ⟨?_, ?_, ?_, ⟨one, honeLt, ?_⟩⟩
      · exact spec.mpFrame 256 256 256 0 mm _ (by omega)
          (Or.inr (by omega)) ih.modulus
      · exact spec.mpValue 256 256 256 _ _ _
          (by omega) (by omega) (by omega) ih.modulus hf.minvW
          ih.accBlock ih.accBlock (fixedValue_lt hm hbM t)
          (fixedValue_lt hm hbM t)
      · exact spec.mpFrame 256 256 256 512 bM _ (by omega)
          (Or.inl (by omega)) ih.baseBlock
      · exact spec.mpFrame 256 256 256 768 one _ (by omega)
          (Or.inl (by omega)) honeRep

end Challenge.Modexp.Submission.Proofs.Fast.FixedExponentLogic
