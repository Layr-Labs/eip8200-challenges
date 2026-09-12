import Challenge.Modexp.Submission.Proofs.Fast.SquareResult
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyExtra

set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
# Cache invariants across the machine-carry square rows

The square analogues of `CarryFull.readonlyCache_rowsCarry`,
`CarryFull.extraCache_rowsCarry` and `CarryFull.inverse_rowsCarry`, for the
square-row loop invariant (and for the states inside a row: after the
prologue and after every chain step).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareCaches

open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCachedMidMemory SquareModel SquareResult

theorem readonlyCache_sqRowsCarry {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) (hn : n ≤ 8) (i : Nat) (hi : i ≤ n) :
    CiosReadonly.ReadonlyCache (sqRowsCarry mem n i) n tl inv m0 :=
  hc.of_preserved
    (readWord_sqRowsCarry mem n 2816 hn (Or.inr (by decide)) i hi)
    (readWord_sqRowsCarry mem n (32 * n - 32) hn (Or.inl (by omega)) i hi)

theorem extraCache_sqRowsCarry {mem : ByteArray} {m96 m64 m32 : UInt256}
    (hc : CiosReadonlyExtra.ExtraCache mem m96 m64 m32) (n : Nat) (hn : n ≤ 8) (i : Nat)
    (hi : i ≤ n) :
    CiosReadonlyExtra.ExtraCache (sqRowsCarry mem n i) m96 m64 m32 :=
  hc.of_preserved
    (readWord_sqRowsCarry mem n 96 hn (Or.inl (by decide)) i hi)
    (readWord_sqRowsCarry mem n 64 hn (Or.inl (by decide)) i hi)
    (readWord_sqRowsCarry mem n 32 hn (Or.inl (by decide)) i hi)

theorem inverse_sqRowsCarry (mem : ByteArray) (n : Nat) (hn : n ≤ 8)
    (hminv : inverseInvariant mem n) (i : Nat) (hi : i ≤ n) :
    inverseInvariant (sqRowsCarry mem n i) n := by
  unfold inverseInvariant at *
  rw [readWord_sqRowsCarry mem n (32 * n - 32) hn (Or.inl (by omega)) i hi,
    readWord_sqRowsCarry mem n 2816 hn (Or.inr (by decide)) i hi]
  exact hminv

/-! Inside one row: after the prologue and after every chain step. -/

theorem readonlyCache_sqPro {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) (hn : n ≤ 8) (i : Nat) (hi : i < n)
    (tb : UInt256) :
    CiosReadonly.ReadonlyCache (sqPro mem n i tb).memory n tl inv m0 :=
  hc.of_preserved
    (readWord_sqPro mem n i 2816 tb hi (Or.inr (by omega)))
    (readWord_sqPro mem n i (32 * n - 32) tb hi (Or.inl (by omega)))

theorem readonlyCache_l1Run {q : MacState} {n : Nat} {tl inv m0 : UInt256}
    (hc : CiosReadonly.ReadonlyCache q.memory n tl inv m0) (hn : n ≤ 8) (bi : UInt256)
    (pa j0 k : Nat) (hk : j0 + k ≤ n) :
    CiosReadonly.ReadonlyCache (l1Run q bi pa n j0 k).memory n tl inv m0 :=
  hc.of_preserved
    (readWord_l1Run q bi pa n j0 2816 (Or.inr (by omega)) k hk)
    (readWord_l1Run q bi pa n j0 (32 * n - 32) (Or.inl (by omega)) k hk)

theorem extraCache_sqPro {mem : ByteArray} {m96 m64 m32 : UInt256}
    (hc : CiosReadonlyExtra.ExtraCache mem m96 m64 m32) (n i : Nat) (hi : i < n)
    (tb : UInt256) :
    CiosReadonlyExtra.ExtraCache (sqPro mem n i tb).memory m96 m64 m32 :=
  hc.of_preserved
    (readWord_sqPro mem n i 96 tb hi (Or.inl (by decide)))
    (readWord_sqPro mem n i 64 tb hi (Or.inl (by decide)))
    (readWord_sqPro mem n i 32 tb hi (Or.inl (by decide)))

theorem extraCache_l1Run {q : MacState} {m96 m64 m32 : UInt256}
    (hc : CiosReadonlyExtra.ExtraCache q.memory m96 m64 m32) (bi : UInt256) (pa n j0 k : Nat)
    (hk : j0 + k ≤ n) :
    CiosReadonlyExtra.ExtraCache (l1Run q bi pa n j0 k).memory m96 m64 m32 :=
  hc.of_preserved
    (readWord_l1Run q bi pa n j0 96 (Or.inl (by decide)) k hk)
    (readWord_l1Run q bi pa n j0 64 (Or.inl (by decide)) k hk)
    (readWord_l1Run q bi pa n j0 32 (Or.inl (by decide)) k hk)

theorem inverse_sqPro (mem : ByteArray) (n i : Nat) (tb : UInt256) (hn : n ≤ 8) (hi : i < n)
    (hminv : inverseInvariant mem n) :
    inverseInvariant (sqPro mem n i tb).memory n := by
  unfold inverseInvariant at *
  rw [readWord_sqPro mem n i (32 * n - 32) tb hi (Or.inl (by omega)),
    readWord_sqPro mem n i 2816 tb hi (Or.inr (by omega))]
  exact hminv

theorem inverse_l1Run (q : MacState) (bi : UInt256) (pa n j0 k : Nat) (hn : n ≤ 8)
    (hk : j0 + k ≤ n) (hminv : inverseInvariant q.memory n) :
    inverseInvariant (l1Run q bi pa n j0 k).memory n := by
  unfold inverseInvariant at *
  rw [readWord_l1Run q bi pa n j0 (32 * n - 32) (Or.inl (by omega)) k hk,
    readWord_l1Run q bi pa n j0 2816 (Or.inr (by omega)) k hk]
  exact hminv

end Challenge.Modexp.Submission.Proofs.Fast.SquareCaches
