import Challenge.Modexp.Submission.Proofs.Fast.LazyCsubMemory
import Challenge.Modexp.Submission.Proofs.Fast.LazyBounds
import Challenge.Modexp.Submission.Proofs.Fast.SquareResult
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
import Challenge.Modexp.Submission.Proofs.Fast.R4Bridge

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareModel SquareResult SquareLoopBlocks

theorem accumulator_congr {a b : ByteArray} (n : Nat)
    (hhigh : MachineState.readWord a 2080 = MachineState.readWord b 2080)
    (hlow : ∀ k, k < n → MachineState.readWord a (2112 + 32*(n-1-k)) =
      MachineState.readWord b (2112 + 32*(n-1-k))) : tValue a n = tValue b n := by
  unfold tValue
  rw [hhigh, Csub.lowValue_congr hlow]

theorem count_accumulator (mem : ByteArray) (n c : Nat) (hn : n ≤ 8) :
    tValue (countMem mem c) n = tValue mem n := by
  apply accumulator_congr
  · exact readWord_countMem_disjoint mem c 2080 (by omega)
  · intro k hk
    exact readWord_countMem_disjoint mem c (2112+32*(n-1-k)) (by omega)

theorem carry_accumulator (mem : ByteArray) (n : Nat) (hn : n ≤ 8) :
    tValue (sqRowsCarry mem n n) n = tValue (sqRowsMem mem n n) n := by
  have h := sqRows_agree mem n hn n le_rfl
  apply accumulator_congr
  · exact CarryScratchAgreement.readWord_eq h 2080 (Or.inr (by omega))
  · intro k _
    exact CarryScratchAgreement.readWord_eq h (2112+32*(n-1-k)) (Or.inr (by omega))

def roundValue (mem : ByteArray) (n mm : Nat) : Nat :=
  LazyCsub.value (Limbs.radix ^ n) mm (tValue mem n)

theorem result_from_square_equation (mem : ByteArray) (n a mm Q pdst : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (ha : a < Limbs.radix ^ n)
    (hm : Model.FastRepresents mem 0 n mm) (hodd : mm % 2 = 1)
    (hQ : Q < Limbs.radix ^ n)
    (heq : tValue mem n * Limbs.radix ^ n = a*a + Q*mm) :
    Model.FastRepresents (LazyCsub.resultMemory mem n pdst) pdst n (roundValue mem n mm) ∧
      roundValue mem n mm < Limbs.radix ^ n ∧
      roundValue mem n mm % mm = Model.montMul mm (Limbs.radix ^ n) a a := by
  have hmpos : 0 < mm := by omega
  have hR : 0 < Limbs.radix ^ n := pow_pos Limbs.radix_pos _
  have hv : tValue mem n = LazyBounds.redc (Limbs.radix^n) mm a a Q := by
    unfold LazyBounds.redc
    rw [← heq, Nat.mul_div_assoc _ (dvd_refl _), Nat.div_self hR, Nat.mul_one]
  have hbounds := LazyBounds.redc_radix_bounds hmpos hm.1 ha ha hQ
  have hbound : tValue mem n < Limbs.radix^n + mm := by rw [hv]; exact hbounds.1
  have htn : (MachineState.readWord mem 2080).toNat ≤ 1 :=
    LazyBounds.top_limb_le_one (hbound.trans hbounds.2) rfl
  refine ⟨?_, LazyCsub.value_lt_radix hm.1 hbound, ?_⟩
  · exact LazyCsub.result_represents mem n (Csub.lowValue mem 2112 n n) mm
      (MachineState.readWord mem 2080).toNat pdst hn hn32
      (Csub.fastRepresents_lowValue mem 2112 n) hm rfl htn hbound
  · rw [roundValue, LazyCsub.value_mod hm.1]
    exact (Model.montMul_eq_mod_of_mul_eq hmpos (Model.coprime_radix_pow_of_odd hodd n) heq).symm

theorem carry_result (mem : ByteArray) (p a mm c pdst : Nat)
    (hn : p+2 ≤ 8)
    (ha : Model.FastRepresents mem 2368 (p+2) a)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (hodd : mm % 2 = 1)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0)
    (hz : tValue mem (p+2) = 0) :
    let after := countMem (sqRowsCarry mem (p+2) (p+2)) c
    Model.FastRepresents (LazyCsub.resultMemory after (p+2) pdst) pdst (p+2)
      (roundValue after (p+2) mm) ∧
      roundValue after (p+2) mm < Limbs.radix^(p+2) ∧
      roundValue after (p+2) mm % mm = Model.montMul mm (Limbs.radix^(p+2)) a a := by
  dsimp only
  obtain ⟨Q, hQ, heq, _, _⟩ := LazyBounds.current_sqRows_lazy mem p a mm hn ha hm
    (by omega) hminv hz
  have hc : tValue (countMem (sqRowsCarry mem (p+2) (p+2)) c) (p+2) =
      tValue (sqRowsMem mem (p+2) (p+2)) (p+2) := by
    rw [count_accumulator _ _ _ hn, carry_accumulator mem (p+2) hn]
  have hm' : Model.FastRepresents (countMem (sqRowsCarry mem (p+2) (p+2)) c) 0 (p+2) mm := by
    refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
    intro j hj
    rw [readWord_countMem_disjoint _ c (0+32*j) (by omega),
      readWord_sqRowsCarry mem (p+2) (0+32*j) hn (Or.inl (by omega)) (p+2) le_rfl]
  apply result_from_square_equation _ (p+2) a mm Q pdst (by omega) hn ha.1 hm' hodd hQ
  rw [hc]
  exact heq

theorem r4_result (mem : ByteArray) (a mm c pdst : Nat)
    (ha : Model.FastRepresents mem 2368 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hodd : mm % 2 = 1)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    let after := countMem (R4Bridge.rows4 mem) c
    Model.FastRepresents (LazyCsub.resultMemory after 4 pdst) pdst 4 (roundValue after 4 mm) ∧
      roundValue after 4 mm < Limbs.radix^4 ∧
      roundValue after 4 mm % mm = Model.montMul mm (Limbs.radix^4) a a := by
  dsimp only
  obtain ⟨Q, hQ, heq⟩ := R4Bridge.rows4_eq mem a mm ha hm hminv
  have hm' : Model.FastRepresents (countMem (R4Bridge.rows4 mem) c) 0 4 mm := by
    refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
    intro j hj
    rw [readWord_countMem_disjoint _ c (0+32*j) (by omega),
      R4Bridge.rows4_readWord_outside mem (0+32*j) (Or.inl (by omega))]
  apply result_from_square_equation _ 4 a mm Q pdst (by omega) (by omega) ha.1 hm' hodd hQ
  rw [count_accumulator _ _ _ (by omega)]
  exact heq

theorem carry_tn_le_one (mem : ByteArray) (p a mm : Nat) (hn : p+2 ≤ 8)
    (ha : Model.FastRepresents mem 2368 (p+2) a)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0)
    (hz : tValue mem (p+2) = 0) :
    (MachineState.readWord (sqRowsCarry mem (p+2) (p+2)) 2080).toNat ≤ 1 := by
  rw [CarryScratchAgreement.readWord_eq (sqRows_agree mem (p+2) hn (p+2) le_rfl) 2080 (Or.inr (by omega))]
  exact LazyBounds.current_sqRows_lazy_tn_le_one mem p a mm hn ha hm hmpos hminv hz

theorem r4_tn_le_one (mem : ByteArray) (a mm : Nat)
    (ha : Model.FastRepresents mem 2368 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    (MachineState.readWord (R4Bridge.rows4 mem) 2080).toNat ≤ 1 := by
  obtain ⟨Q, hQ, heq⟩ := R4Bridge.rows4_eq mem a mm ha hm hminv
  have hR : 0 < Limbs.radix^4 := pow_pos Limbs.radix_pos _
  have hv : tValue (R4Bridge.rows4 mem) 4 = LazyBounds.redc (Limbs.radix^4) mm a a Q := by
    unfold LazyBounds.redc
    rw [← heq, Nat.mul_div_assoc _ (dvd_refl _), Nat.div_self hR, Nat.mul_one]
  have hb := LazyBounds.redc_radix_bounds hmpos hm.1 ha.1 ha.1 hQ
  apply LazyBounds.top_limb_le_one (R := Limbs.radix^4)
    (u := tValue (R4Bridge.rows4 mem) 4)
    (low := Csub.lowValue (R4Bridge.rows4 mem) 2112 4 4)
  · rw [hv]
    exact hb.1.trans hb.2
  · rfl

end Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory
