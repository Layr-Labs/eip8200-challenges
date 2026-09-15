import Challenge.Modexp.Submission.Proofs.Fast.LazyBounds
import Challenge.Modexp.Submission.Proofs.Fast.StagedProduct

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.LazyMixedProduct
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro StagedMonpro

private theorem div_of_mul {x y r : Nat} (hr : 0 < r) (h : x * r = y) : y / r = x := by
  rw [← h, Nat.mul_div_assoc _ (dvd_refl _), Nat.div_self hr, Nat.mul_one]

theorem rows_invariant_lazy (s : State) (mem : ByteArray) (pa pb p : Nat) (a b mm : Nat)
    (hn32 : p + 2 ≤ 8)
    (hpaFit : pa + 32 * (p + 2) ≤ 2048 ∨ 2368 ≤ pa) (hpbFit : pb + 32 * (p + 2) ≤ 2048)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    ∀ i, i ≤ p + 2 → ∃ Q, Q < Limbs.radix ^ i ∧
      tValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) (p + 2) *
          Limbs.radix ^ i = a * (b % Limbs.radix ^ i) + Q * mm ∧
        tValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) (p + 2) < a + mm := by
  intro i
  induction i with
  | zero =>
      intro _
      have hlow0 : Csub.lowValue (mpZeroed s mem (p + 2)) 2112 (p + 2) (p + 2) = 0 :=
        Model.fastRepresents_value_unique
          (Csub.fastRepresents_lowValue (mpZeroed s mem (p + 2)) 2112 (p + 2))
          (fastRepresents_mpZeroed s mem (p + 2))
      have hzero : tValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) 0)
          (p + 2) = 0 := by
        show tValue (mpZeroed s mem (p + 2)) (p + 2) = 0
        simp only [tValue, hlow0, readWord_mpZeroed_tn,
          Challenge.EvmProof.Word.word_toNat_ofNat]
        simp
      exact ⟨0, by simp, by rw [hzero, pow_zero, Nat.mod_one]; simp, by rw [hzero]; omega⟩
  | succ i ih =>
      intro hi
      obtain ⟨Q, hQ, hinv, hlt⟩ := ih (by omega)
      simp only [tValue] at hinv hlt ⊢
      simp only [rowsMem]
      have hpaR : Model.FastRepresents
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) pa (p + 2) a :=
        StagedMonpro.fastRepresents_monpro_preserved s mem pa pb (p + 2) i pa (p + 2) a hn32
          hpaFit ha
      have hpbR : Model.FastRepresents
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) pb (p + 2) b :=
        StagedMonpro.fastRepresents_monpro_preserved s mem pa pb (p + 2) i pb (p + 2) b hn32
          (Or.inl hpbFit) hb
      have hmR : Model.FastRepresents
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 0 (p + 2) mm :=
        StagedMonpro.fastRepresents_monpro_preserved s mem pa pb (p + 2) i 0 (p + 2) mm hn32
          (by omega) hm
      have hminvR : ((MachineState.readWord
            (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
            (32 * (p + 2) - 32)).toNat *
          (MachineState.readWord
            (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2720).toNat + 1) %
          2 ^ 256 = 0 := by
        rw [StagedMonpro.readWord_monpro_preserved s mem pa pb (p + 2) i (32 * (p + 2) - 32) hn32
            (Or.inl (by omega)),
          StagedMonpro.readWord_monpro_preserved s mem pa pb (p + 2) i 2720 hn32 (Or.inr (by omega))]
        exact hminv
      have hrow := row_equation (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
        pa pb p i a mm
        (Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2112
          (p + 2) (p + 2))
        hn32 hpaFit hpaR hmR
        (Csub.fastRepresents_lowValue
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2112 (p + 2)) hminvR
      have hbi : (rowBi (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pb (p + 2) i).toNat = b / Limbs.radix ^ i % Limbs.radix := by
        simp only [rowBi]
        exact Model.readLimb_of_fastRepresents hpbR (by omega)
      have hdiv : Limbs.radix ∣
          (MachineState.readWord (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              2080).toNat * Limbs.radix ^ (p + 2) +
            Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2112
              (p + 2) (p + 2) +
            a * (rowBi (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pb (p + 2) i).toNat +
            (rowMu (rowL1 (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pa pb (p + 2) i).memory (p + 2)).toNat * mm := by
        refine ⟨(MachineState.readWord (rowMem
              (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) pa pb (p + 2) i)
              2080).toNat * Limbs.radix ^ (p + 2) +
            Csub.lowValue (rowMem (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pa pb (p + 2) i) 2112 (p + 2) (p + 2), ?_⟩
        rw [← hrow]
        ring
      have hquot := div_of_mul Limbs.radix_pos hrow
      obtain ⟨hstep1, hstep2, hstepQ⟩ := LazyBounds.cios_step_lazy (β := Limbs.radix) (m := mm) (a := a)
        (bpre := b % Limbs.radix ^ i)
        (bi := (rowBi (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pb (p + 2) i).toNat)
        (t := (MachineState.readWord
            (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2080).toNat *
            Limbs.radix ^ (p + 2) +
          Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2112
            (p + 2) (p + 2))
        (Q := Q)
        (mu := (rowMu (rowL1 (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pa pb (p + 2) i).memory (p + 2)).toNat) (i := i)
        Limbs.radix_pos (word_lt_size _) hlt (word_lt_size _) hQ hinv hdiv
      refine ⟨Q + (rowMu (rowL1 (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
        pa pb (p + 2) i).memory (p + 2)).toNat * Limbs.radix ^ i, hstepQ, ?_, ?_⟩
      · rw [← hquot, hstep1, mod_pow_succ, hbi]
      · rw [← hquot]
        exact hstep2

theorem rows_final (s : State) (mem : ByteArray) (pa pb p a b mm : Nat)
    (hn : p+2 ≤ 8)
    (hpa : pa+32*(p+2) ≤ 2048 ∨ 2368 ≤ pa) (hpb : pb+32*(p+2) ≤ 2048)
    (ha : Model.FastRepresents mem pa (p+2) a)
    (hb : Model.FastRepresents mem pb (p+2) b)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (hbm : b < mm)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    ∃ Q, Q < Limbs.radix^(p+2) ∧
      tValue (rowsMem (mpZeroed s mem (p+2)) pa pb (p+2) (p+2)) (p+2) *
        Limbs.radix^(p+2) = a*b+Q*mm ∧
      tValue (rowsMem (mpZeroed s mem (p+2)) pa pb (p+2) (p+2)) (p+2) < 2*mm := by
  obtain ⟨Q, hQ, heq, _⟩ := rows_invariant_lazy s mem pa pb p a b mm hn hpa hpb ha hb hm
    (by omega) hminv (p+2) le_rfl
  rw [Nat.mod_eq_of_lt hb.1] at heq
  have hR : 0 < Limbs.radix^(p+2) := pow_pos Limbs.radix_pos _
  have hv : tValue (rowsMem (mpZeroed s mem (p+2)) pa pb (p+2) (p+2)) (p+2) =
      LazyBounds.redc (Limbs.radix^(p+2)) mm a b Q := by
    unfold LazyBounds.redc
    rw [← heq, Nat.mul_div_assoc _ (dvd_refl _), Nat.div_self hR, Nat.mul_one]
  exact ⟨Q, hQ, heq, hv ▸ LazyBounds.redc_mixed_canonical_lt_two hR (by omega) ha.1 hbm hQ⟩

theorem represents (s : State) (mem : ByteArray) (p a b mm : Nat)
    (hn : p+2 ≤ 8)
    (ha : Model.FastRepresents mem 2368 (p+2) a)
    (hb : Model.FastRepresents mem 256 (p+2) b)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (hodd : mm % 2 = 1) (hbm : b < mm)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    Model.FastRepresents (StagedProduct.memory s mem (p+2)) 256 (p+2)
      (Model.montMul mm (Limbs.radix^(p+2)) a b) := by
  obtain ⟨Q, _, heq, hlt⟩ := rows_final s mem 2368 256 p a b mm hn (by omega) (by omega)
    ha hb hm hbm hminv
  have ht : (MachineState.readWord (rowsMem (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2)) 2080).toNat ≤ 1 := by
    apply LazyBounds.top_limb_le_one (low := Csub.lowValue _ 2112 (p+2) (p+2))
    · exact lt_trans hlt (Nat.mul_lt_mul_of_pos_left hm.1 (by decide))
    · rfl
  have hmod : Model.FastRepresents (rowsMem (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2)) 0 (p+2) mm :=
    StagedMonpro.fastRepresents_monpro_preserved s mem 2368 256 (p+2) (p+2) 0 (p+2) mm hn (by omega) hm
  have hvalue : Model.montMul mm (Limbs.radix^(p+2)) a b =
      tValue (rowsMem (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2)) (p+2) % mm :=
    Model.montMul_eq_mod_of_mul_eq (by omega) (Model.coprime_radix_pow_of_odd hodd (p+2)) heq
  have hr := Csub.csub_correct (rowsMem (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2))
    (p+2) (Csub.lowValue _ 2112 (p+2) (p+2)) mm
    (MachineState.readWord (rowsMem (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2)) 2080).toNat
    256 (by omega) hn (Csub.fastRepresents_lowValue _ 2112 (p+2)) hmod rfl ht (by omega) hlt
  have hg := StagedProduct.rows_agree (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2)
    (by omega) (by omega) (by omega) hn le_rfl
  have hc := CarryRowModel.csResult_agree _ _ hg (p+2) 256 (by omega) hn ht
  rw [StagedProduct.memory, hvalue]
  exact (CarryRowModel.fastRepresents_iff _ _ hc 256 (p+2) _ (Or.inl (by omega))).2 hr

theorem rows_tn_le_one (s : State) (mem : ByteArray) (p a b mm : Nat)
    (hn : p+2 ≤ 8)
    (ha : Model.FastRepresents mem 2368 (p+2) a)
    (hb : Model.FastRepresents mem 256 (p+2) b)
    (hm : Model.FastRepresents mem 0 (p+2) mm)
    (_har : a < Limbs.radix^(p+2)) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    (MachineState.readWord (CarryRowModel.rowsCarry (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2)) 2080).toNat ≤ 1 := by
  obtain ⟨_, _, _, ht⟩ := rows_invariant_lazy s mem 2368 256 p a b mm hn (by omega) (by omega)
    ha hb hm hmpos hminv (p+2) le_rfl
  have hu : tValue (rowsMem (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2)) (p+2) <
      2*Limbs.radix^(p+2) := by have := ha.1; have := hm.1; omega
  have htn := LazyBounds.top_limb_le_one (low := Csub.lowValue
    (rowsMem (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2)) 2112 (p+2) (p+2)) hu rfl
  rw [CarryScratchAgreement.readWord_eq
    (StagedProduct.rows_agree (mpZeroed s mem (p+2)) 2368 256 (p+2) (p+2)
      (by omega) (by omega) (by omega) hn le_rfl) 2080 (Or.inr (by omega))]
  exact htn

end Challenge.Modexp.Submission.Proofs.Fast.LazyMixedProduct
