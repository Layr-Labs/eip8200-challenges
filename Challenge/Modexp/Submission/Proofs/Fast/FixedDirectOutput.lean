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

/-- Memory after the caller's square loop has run down from `k` remaining
in-place Montgomery squares of BASE, `sq` being the memory effect of one
`SQUARE(0x800) → 0x800` call.  Each iteration first stores the remaining count
in memory word `0x2440 = 5184` (the loop head's `MSTORE`, read by the kernel's
own square loop) and then calls the kernel. -/
def fixedDirectMems
    (sq : ByteArray → ByteArray) : ByteArray → Nat → ByteArray
  | mem, 0 => mem
  | mem, k + 1 =>
      fixedDirectMems sq (sq (Exp.storeWord mem 5184 (UInt256.ofNat (k + 1)))) k

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

/-- Squaring first and then iterating is the whole chain. -/
theorem fixedDirectValue_step (mm R bM : Nat) : ∀ t,
    fixedDirectValue mm R (Model.montMul mm R bM bM) t =
      fixedDirectValue mm R bM (t + 1) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp only [fixedDirectValue, ih]

/-- The chain value in the iterate form the kernel's loop lemma uses. -/
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

/-- The blocks carried by the direct fixed chain. ACC deliberately remains a
normal-domain residue while BASE is in Montgomery form. -/
structure Inv (mem : ByteArray) (n mm rawBase squareBase : Nat) : Prop where
  modulus : Model.FastRepresents mem 0 n mm
  rawAcc : Model.FastRepresents mem 256 n rawBase
  squareBase : Model.FastRepresents mem 512 n squareBase
  oneBlock : ∃ one, one < Limbs.radix ∧
    Model.FastRepresents mem 768 n one

/-- The square count the loop head writes sits at `0x2440`, above every block
the chain reads and below the configuration words. -/
theorem countStore_frame {mem : ByteArray} {n bsize minv : Nat} (c : Nat)
    (hframe : Exp.Frame mem n bsize minv) :
    Exp.Frame (Exp.storeWord mem 5184 (UInt256.ofNat c)) n bsize minv :=
  Exp.frame_storeWord (UInt256.ofNat c) (by omega) hframe

/-- The square count the loop head writes disturbs no block of the chain. -/
theorem countStore_inv {mem : ByteArray} {n mm rawBase squareBase : Nat} (c : Nat)
    (hn32 : n ≤ 32) (hinv : Inv mem n mm rawBase squareBase) :
    Inv (Exp.storeWord mem 5184 (UInt256.ofNat c)) n mm rawBase squareBase := by
  obtain ⟨one, honeLt, honeRep⟩ := hinv.oneBlock
  exact ⟨Exp.storeWord_frame mem 5184 0 n mm _ (Or.inr (by omega)) hinv.modulus,
    Exp.storeWord_frame mem 5184 1024 n rawBase _ (Or.inr (by omega)) hinv.rawAcc,
    Exp.storeWord_frame mem 5184 2048 n squareBase _ (Or.inr (by omega))
      hinv.squareBase,
    ⟨one, honeLt,
      Exp.storeWord_frame mem 5184 3072 n one _ (Or.inr (by omega)) honeRep⟩⟩

theorem fixedDirectMems_frame {s : State} {n bsize mm minv : Nat}
    (sub : Exp.Subroutines s n bsize mm minv) :
    ∀ (t : Nat) (mem : ByteArray), Exp.Frame mem n bsize minv →
      Exp.Frame (fixedDirectMems sub.sqMem mem t) n bsize minv := by
  intro t
  induction t with
  | zero => exact fun _ hframe => hframe
  | succ t ih =>
      exact fun mem hframe =>
        ih _ (sub.sqFrame _ (countStore_frame (t + 1) hframe))

/-- In-place BASE squaring preserves modulus, raw ACC, and ONE. -/
theorem fixedDirectMems_inv {s : State} {n bsize mm minv : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (hm : 0 < mm) (hn32 : n ≤ 32) (rawBase : Nat) :
    ∀ (t : Nat) (mem : ByteArray) (bM : Nat), bM < mm →
      Exp.Frame mem n bsize minv → Inv mem n mm rawBase bM →
      Inv (fixedDirectMems sub.sqMem mem t) n mm rawBase
        (fixedDirectValue mm (Limbs.radix ^ n) bM t) := by
  intro t
  induction t with
  | zero => exact fun _ _ _ _ hinv => hinv
  | succ t ih =>
      intro mem bM hbM hframe hinv
      have hinv0 := countStore_inv (t + 1) hn32 hinv
      have hframe0 := countStore_frame (t + 1) hframe
      obtain ⟨one, honeLt, honeRep⟩ := hinv0.oneBlock
      have hstep : Inv (sub.sqMem (Exp.storeWord mem 5184 (UInt256.ofNat (t + 1))))
          n mm rawBase (Model.montMul mm (Limbs.radix ^ n) bM bM) :=
        ⟨sub.sqKeep 0 mm _ (by omega) (Or.inr (by omega)) hinv0.modulus,
         sub.sqKeep 1024 rawBase _ (by omega) (Or.inr (by omega)) hinv0.rawAcc,
         sub.sqValue _ _ hframe0 hinv0.modulus hinv0.squareBase hbM,
         ⟨one, honeLt, sub.sqKeep 3072 one _ (by omega) (Or.inl (by omega)) honeRep⟩⟩
      have hrec := ih _ _ (Model.montMul_lt hm (Limbs.radix ^ n) bM bM)
        (sub.sqFrame _ hframe0) hstep
      rw [fixedDirectValue_step] at hrec
      exact hrec

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
