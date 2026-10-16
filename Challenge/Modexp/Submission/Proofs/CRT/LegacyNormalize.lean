import Challenge.Modexp.Submission.Proofs.CRT.MixedMontgomery
import Challenge.Modexp.Submission.Proofs.Fast.SquareRoundC
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.LegacyNormalize
open EvmSemantics
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.MixedMontgomery

theorem old_radix : Limbs.radix^8 = (2^2048 : Nat) := by
  change (2^256)^8 = (2^2048 : Nat)
  rw [← Nat.pow_mul]

/-- The rare path always copies SUBB. Its arithmetic is independent of the
stale row-head flag at2080; the actual subtraction borrow gives the result. -/
theorem sub8_represents (mem : ByteArray) (Q N : Nat)
    (ht : Model.FastRepresents mem 2112 8 (Q % 2^2048))
    (hm : Model.FastRepresents mem 0 8 N)
    (hQR : 2^2048 ≤ Q) (hQ : Q < 2^2048+N) :
    Model.FastRepresents (SquareRoundC.sub8 mem) 2368 8 (Q-N) := by
  have hN : N < 2^2048 := by simpa only [old_radix] using hm.1
  have hdiff : Q-2^2048 < 2^2048 := by omega
  have hlow : Q % 2^2048 = Q-2^2048 := by
    rw [Nat.mod_eq_sub_mod hQR, Nat.mod_eq_of_lt hdiff]
  have htotal : Q = 2^2048 + Q % 2^2048 := by omega
  have hlt : Q % 2^2048 < N := by omega
  obtain ⟨hinv, hbor⟩ := Csub.csStep_invariant mem 8 (by decide) (by decide) 8 le_rfl
  have hM : Csub.lowValue mem 0 8 8 = N := by
    rw [Csub.lowValue_full]; exact Model.value_of_fastRepresents hm
  have hT : Csub.lowValue mem 2112 8 8 = Q % 2^2048 := by
    rw [Csub.lowValue_full]; exact Model.value_of_fastRepresents ht
  rw [hM, hT, old_radix] at hinv
  have hb1 : (Csub.csStep mem 8 8).flag.toNat = 1 := by
    by_contra hb
    have hb0 : (Csub.csStep mem 8 8).flag.toNat = 0 := by omega
    rw [hb0, Nat.zero_mul, Nat.add_zero] at hinv
    omega
  rw [hb1, Nat.one_mul] at hinv
  have hv : Csub.lowValue (Csub.csStep mem 8 8).memory 1792 8 8 = Q-N := by omega
  have hr := Csub.fastRepresents_lowValue (Csub.csStep mem 8 8).memory 1792 8
  rw [hv] at hr
  exact Csub.fastRepresents_mcopy _ 1792 2368 8 (Q-N) (by decide) hr

/-- The old rare exit first stores the row-head flag at2080. The stored
flag cannot affect the represented result at2368. -/
theorem sub8_lift_represents (mem : ByteArray) (Q N : Nat) (flag : UInt256)
    (ht : Model.FastRepresents mem 2112 8 (Q % 2^2048))
    (hm : Model.FastRepresents mem 0 8 N)
    (hQR : 2^2048 ≤ Q) (hQ : Q < 2^2048+N) :
    Model.FastRepresents (SquareRoundC.sub8 (TnCacheMemory.lift mem flag)) 2368 8 (Q-N) := by
  rw [SquareRoundC.sub8_lift]
  apply (Model.fastRepresents_congr (fun j hj =>
    TnCacheMemory.read_lift_outside _ flag (2368+32*j) (Or.inr (by omega))) (Q-N)).2
  exact sub8_represents mem Q N ht hm hQR hQ

/-- Ordinary exit, including the old copy and overflow subtraction branches. -/
def correctedMemory (mem : ByteArray) (Q : Nat) : ByteArray :=
  if Q < 2^2048 then SquareRoundC.copy8 mem else SquareRoundC.sub8 mem

theorem corrected_represents (mem : ByteArray) (Q N : Nat)
    (ht : Model.FastRepresents mem 2112 8 (Q % 2^2048))
    (hm : Model.FastRepresents mem 0 8 N) (hQ : Q < 2^2048+N) :
    Model.FastRepresents (correctedMemory mem Q) 2368 8 (HistoricalSearch.MixedMontgomery.normalize (2^2048) N Q) := by
  unfold correctedMemory HistoricalSearch.MixedMontgomery.normalize
  by_cases h : Q < 2^2048
  · rw [if_pos h, if_neg (by omega)]
    rw [Nat.mod_eq_of_lt h] at ht
    exact Csub.fastRepresents_mcopy mem 2112 2368 8 Q (by decide) ht
  · rw [if_neg h, if_pos (by omega)]
    exact sub8_represents mem Q N ht hm (by omega) hQ

theorem corrected_word_live (mem : ByteArray) (Q addr : Nat)
    (hd : addr+32 ≤ 1792 ∨ 2624 ≤ addr) :
    MachineState.readWord (correctedMemory mem Q) addr = MachineState.readWord mem addr := by
  unfold correctedMemory
  split
  · exact SquareRoundC.copy8_readWord mem addr (by omega)
  · exact SquareRoundC.sub8_readWord mem addr hd

#print axioms sub8_represents
#print axioms sub8_lift_represents
#print axioms corrected_represents
#print axioms corrected_word_live
end HistoricalSearch.LegacyNormalize
