import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Retained-base invariant for direct fixed-exponent output

The generic fixed route copies Montgomery BASE into ACC and later decodes with
ONE. The direct successor instead keeps the reduced normal-domain base in ACC,
squares Montgomery BASE in place, and performs one final mixed-domain product.

This module is an arithmetic/interface layer. Concrete located instruction
traces are kept in separate bytecode modules.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs

/-- Memory after `t` in-place Montgomery squares of BASE. -/
def fixedDirectMems
    (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (mem : ByteArray) : Nat → ByteArray
  | 0 => mem
  | t + 1 => mpMem 2048 2048 2048 (fixedDirectMems mpMem mem t)

/-- Moving the first in-place square before the remaining iterations does
not change the memory reached by the complete chain. -/
theorem fixedDirectMems_step_add
    (mpMem : Nat → Nat → Nat → ByteArray → ByteArray)
    (mem : ByteArray) (t : Nat) :
    fixedDirectMems mpMem (mpMem 2048 2048 2048 mem) t =
      fixedDirectMems mpMem mem (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [fixedDirectMems, ih]

/-- Arithmetic value represented by BASE after `t` in-place squares. -/
def fixedDirectValue (mm R bM : Nat) : Nat → Nat
  | 0 => bM
  | t + 1 => Model.montMul mm R
      (fixedDirectValue mm R bM t) (fixedDirectValue mm R bM t)

theorem fixedDirectValue_lt {mm R bM : Nat} (hm : 0 < mm)
    (hbM : bM < mm) : ∀ t, fixedDirectValue mm R bM t < mm := by
  intro t
  induction t with
  | zero => exact hbM
  | succ t _ => exact Model.montMul_lt hm _ _ _

theorem fixedDirectValue_form {mm R b bM : Nat} (hm : 0 < mm)
    (hcop : Nat.Coprime R mm) (hbMform : bM ≡ b * R [MOD mm]) :
    ∀ t, fixedDirectValue mm R bM t ≡ b ^ (2 ^ t) * R [MOD mm] := by
  intro t
  induction t with
  | zero => simpa [fixedDirectValue] using hbMform
  | succ t ih =>
      rw [fixedDirectValue]
      have hs := Model.mont_sq_step hm hcop ih
      rw [hs, pow_succ, Nat.mul_comm (2 ^ t) 2]
      exact Nat.mod_modEq _ _

/-- The blocks carried by the direct fixed chain. ACC deliberately remains a
normal-domain residue while BASE is in Montgomery form. -/
structure Inv (mem : ByteArray) (n mm rawBase squareBase : Nat) : Prop where
  modulus : Model.FastRepresents mem 0 n mm
  rawAcc : Model.FastRepresents mem 1024 n rawBase
  squareBase : Model.FastRepresents mem 2048 n squareBase
  oneBlock : ∃ one, one < Limbs.radix ∧
    Model.FastRepresents mem 3072 n one

theorem fixedDirectMems_frame {s : State} {n bsize mm minv : Nat}
    (sub : Exp.Subroutines s n bsize mm minv) (mem : ByteArray)
    (hframe : Exp.Frame mem n bsize minv) :
    ∀ t, Exp.Frame (fixedDirectMems sub.mpMem mem t) n bsize minv := by
  intro t
  induction t with
  | zero => exact hframe
  | succ t ih => exact sub.mpFrame 2048 2048 2048 _ (by omega) ih

/-- In-place BASE squaring preserves modulus, raw ACC, and ONE. -/
theorem fixedDirectMems_inv {s : State} {n bsize mm minv R bM rawBase : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm R minv)
    (mem : ByteArray) (hm : 0 < mm) (hn32 : n ≤ 32) (hbM : bM < mm)
    (hframe : Exp.Frame mem n bsize minv)
    (hinv : Inv mem n mm rawBase bM) :
    ∀ t, Inv (fixedDirectMems sub.mpMem mem t) n mm rawBase
      (fixedDirectValue mm R bM t) := by
  intro t
  induction t with
  | zero => exact hinv
  | succ t ih =>
      have hf := fixedDirectMems_frame sub mem hframe t
      obtain ⟨one, honeLt, honeRep⟩ := ih.oneBlock
      refine ⟨?_, ?_, ?_, ⟨one, honeLt, ?_⟩⟩
      · exact spec.mpFrame 2048 2048 2048 0 mm _ (by omega)
          (Or.inr (by omega)) ih.modulus
      · exact spec.mpFrame 2048 2048 2048 1024 rawBase _ (by omega)
          (Or.inr (by omega)) ih.rawAcc
      · exact spec.mpValue 2048 2048 2048 _ _ _
          (by omega) (by omega) (by omega) ih.modulus hf.minvW
          ih.squareBase ih.squareBase
          (fixedDirectValue_lt hm hbM t) (fixedDirectValue_lt hm hbM t)
      · exact spec.mpFrame 2048 2048 2048 3072 one _ (by omega)
          (Or.inl (by omega)) honeRep

/-- A Montgomery-form left operand times a normal-form right operand is a
normal-domain product. -/
theorem montMul_normal_right {m R x y xM y0 : Nat} (hm : 0 < m)
    (hcop : Nat.Coprime R m) (hx : xM ≡ x * R [MOD m])
    (hy : y0 ≡ y [MOD m]) :
    Model.montMul m R xM y0 = x * y % m := by
  apply Model.montMul_eq_of_modEq hm hcop _ (Nat.mod_lt _ hm)
  calc x * y % m * R ≡ x * y * R [MOD m] :=
        (Nat.mod_modEq (x * y) m).mul_right R
    _ = (x * R) * y := by ring
    _ ≡ xM * y0 [MOD m] := hx.symm.mul hy.symm

/-- The final mixed-domain product is already the normal-domain power. -/
theorem directProduct_value {mm R b bM rawBase count : Nat}
    (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hbMform : bM ≡ b * R [MOD mm]) (hraw : rawBase ≡ b [MOD mm]) :
    Model.montMul mm R (fixedDirectValue mm R bM count) rawBase =
      b ^ (2 ^ count + 1) % mm := by
  rw [montMul_normal_right hm hcop
    (fixedDirectValue_form hm hcop hbMform count) hraw]
  simp only [pow_succ]

/-- Interface for the direct-output implementation of the two fixed cases. -/
structure Handler (s : State) (mem input : ByteArray)
    (n bsize esize msize : Nat) where
  enter : Challenge.EvmProof.GasSteps
    (Exp.bDone s mem n bsize esize msize)
    (FixedExponentRoute.entryState s mem n bsize esize msize)
  miss : ¬ FixedExponentRoute.Matches input bsize esize →
    Challenge.EvmProof.GasSteps
      (FixedExponentRoute.entryState s mem n bsize esize msize)
      (FixedExponentRoute.missState s mem n bsize esize msize)
  hit : ∀ count : Nat, FixedExponentRoute.Case input bsize esize count →
    FixedExponentRoute.Handled input
      (FixedExponentRoute.entryState s mem n bsize esize msize)

/-- Forget implementation details and expose the ordinary fixed route. -/
def Handler.toRoute (handler : Handler s mem input n bsize esize msize) :
    FixedExponentRoute.Route s mem input n bsize esize msize where
  enter := handler.enter
  miss := handler.miss
  hit := by
    rintro ⟨count, hcase⟩
    exact handler.hit count hcase

/-- Compose a direct-output handler with the generic miss proof. -/
def handled_of_bDoneWithGeneric
    (handler : Handler s mem input n bsize esize msize)
    (generic : FixedExponentRoute.Handled input
      (FixedExponentRoute.missState s mem n bsize esize msize)) :
    FixedExponentRoute.Handled input (Exp.bDone s mem n bsize esize msize) := by
  by_cases hmatch : FixedExponentRoute.Matches input bsize esize
  · rcases handler.toRoute.hit hmatch with ⟨final, ⟨tail⟩, hdone, hresult⟩
    exact ⟨final, ⟨handler.enter.trans tail⟩, hdone, hresult⟩
  · rcases generic with ⟨final, ⟨tail⟩, hdone, hresult⟩
    exact ⟨final, ⟨(handler.enter.trans (handler.miss hmatch)).trans tail⟩,
      hdone, hresult⟩

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput
