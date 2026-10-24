import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Retained-base invariant for direct fixed-exponent output

The generic fixed route copies Montgomery BASE into ACC and later decodes with
ONE. The direct successor instead keeps the reduced normal-domain base in ACC,
squares Montgomery BASE in place (the dedicated `SQUARE` kernel, contract
`Exp.Subroutines.square/sqValue/sqKeep`), and performs one final mixed-domain
product (`MONPRO`).

This module is an arithmetic/interface layer. Concrete located instruction
traces are kept in separate bytecode modules.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs


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

theorem fixedDirectValue_step (mm R bM : Nat) : ∀ t,
    fixedDirectValue mm R (Model.montMul mm R bM bM) t =
      fixedDirectValue mm R bM (t + 1) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp only [fixedDirectValue, ih]

theorem fixedDirectValue_eq_iterate (mm R bM : Nat) : ∀ t,
    fixedDirectValue mm R bM t =
      (fun x => Model.montMul mm R x x)^[t] bM := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [fixedDirectValue, Function.iterate_succ_apply', ih]

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

structure Inv (mem : ByteArray) (n mm rawBase squareBase : Nat) : Prop where
  modulus : Model.FastRepresents mem 0 n mm
  rawAcc : Model.FastRepresents mem 256 n rawBase
  squareBase : Model.FastRepresents mem 2112 n squareBase
  oneBlock : ∃ one, one < Limbs.radix ∧
    Model.FastRepresents mem 768 n one

theorem countStore_frame {mem : ByteArray} {n bsize minv : Nat} (c : Nat)
    (hframe : Exp.Frame mem n bsize minv) :
    Exp.Frame (Exp.storeWord mem 2624 (UInt256.ofNat c)) n bsize minv :=
  Exp.frame_storeWord (UInt256.ofNat c) (by omega) hframe

theorem countStore_inv {mem : ByteArray} {n mm rawBase squareBase : Nat} (c : Nat)
    (hn32 : n ≤ 8) (hinv : Inv mem n mm rawBase squareBase) :
    Inv (Exp.storeWord mem 2624 (UInt256.ofNat c)) n mm rawBase squareBase := by
  obtain ⟨one, honeLt, honeRep⟩ := hinv.oneBlock
  exact ⟨Exp.storeWord_frame mem 2624 0 n mm _ (Or.inr (by omega)) hinv.modulus,
    Exp.storeWord_frame mem 2624 256 n rawBase _ (Or.inr (by omega)) hinv.rawAcc,
    Exp.storeWord_frame mem 2624 2112 n squareBase _ (Or.inr (by omega))
      hinv.squareBase,
    ⟨one, honeLt,
      Exp.storeWord_frame mem 2624 768 n one _ (Or.inr (by omega)) honeRep⟩⟩


theorem montMul_normal_right {m R x y xM y0 : Nat} (hm : 0 < m)
    (hcop : Nat.Coprime R m) (hx : xM ≡ x * R [MOD m])
    (hy : y0 ≡ y [MOD m]) :
    Model.montMul m R xM y0 = x * y % m := by
  apply Model.montMul_eq_of_modEq hm hcop _ (Nat.mod_lt _ hm)
  calc x * y % m * R ≡ x * y * R [MOD m] :=
        (Nat.mod_modEq (x * y) m).mul_right R
    _ = (x * R) * y := by ring
    _ ≡ xM * y0 [MOD m] := hx.symm.mul hy.symm

theorem directProduct_value {mm R b bM rawBase count : Nat}
    (hm : 0 < mm) (hcop : Nat.Coprime R mm)
    (hbMform : bM ≡ b * R [MOD mm]) (hraw : rawBase ≡ b [MOD mm]) :
    Model.montMul mm R (fixedDirectValue mm R bM count) rawBase =
      b ^ (2 ^ count + 1) % mm := by
  rw [montMul_normal_right hm hcop
    (fixedDirectValue_form hm hcop hbMform count) hraw]
  simp only [pow_succ]

structure Handler (s : State) (mem input : ByteArray)
    (n bsize esize msize : Nat) where
  enter : Challenge.EvmProof.GasSteps
    (Exp.bDone s mem n bsize esize msize)
    (FixedExponentRoute.entryState s mem n bsize esize msize)
  miss : ¬ FixedExponentRoute.Matches input bsize esize →
    FixedExponentRoute.Handled input
      (FixedExponentRoute.entryState s mem n bsize esize msize)
  hit : ∀ count : Nat, FixedExponentRoute.Case input bsize esize count →
    FixedExponentRoute.Handled input
      (FixedExponentRoute.entryState s mem n bsize esize msize)

def Handler.toRoute (handler : Handler s mem input n bsize esize msize) :
    FixedExponentRoute.Route s mem input n bsize esize msize where
  enter := handler.enter
  miss := handler.miss
  hit := by
    rintro ⟨count, hcase⟩
    exact handler.hit count hcase

def handled_of_bDoneWithGeneric
    (handler : Handler s mem input n bsize esize msize) :
    FixedExponentRoute.Handled input (Exp.bDone s mem n bsize esize msize) := by
  by_cases hmatch : FixedExponentRoute.Matches input bsize esize
  · rcases handler.toRoute.hit hmatch with ⟨final, ⟨tail⟩, hdone, hresult⟩
    exact ⟨final, ⟨handler.enter.trans tail⟩, hdone, hresult⟩
  · rcases handler.miss hmatch with ⟨final, ⟨tail⟩, hdone, hresult⟩
    exact ⟨final, ⟨handler.enter.trans tail⟩, hdone, hresult⟩

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput
