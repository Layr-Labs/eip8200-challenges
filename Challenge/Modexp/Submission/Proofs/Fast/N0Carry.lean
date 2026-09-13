import Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry
import Challenge.Modexp.Submission.Proofs.Fast.R4Math

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.N0Carry
open EvmSemantics
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry

theorem addMod_comm (a b m : UInt256) :
    UInt256.addMod a b m = UInt256.addMod b a m := by
  unfold UInt256.addMod
  split <;> simp only [Nat.add_comm]

/-- Cancellation carries below the all-ones word have a canonical Mersenne residue. -/
theorem cancellation_nat {B q n t c : Nat} (hB : 2 ≤ B)
    (hq : q < B) (hn : n < B - 1) (ht : t < B)
    (hc : q * n + t = B * c) :
    (q * n % (B - 1) + t) % (B - 1) = c := by
  have hp : (q + 1) * n ≤ B * n := Nat.mul_le_mul_right n (by omega)
  have hcn : c ≤ n := by nlinarith
  have hclt : c < B - 1 := by omega
  have hmod : B ≡ 1 [MOD B - 1] := by
    unfold Nat.ModEq
    calc B % (B - 1) = ((B - 1) + 1) % (B - 1) := congrArg (fun z => z % (B - 1)) (by omega)
      _ = 1 % (B - 1) := Nat.add_mod_left _ _
  have hr := hmod.mul_right c
  change (B * c) % (B - 1) = (1 * c) % (B - 1) at hr
  rw [Nat.one_mul, Nat.mod_eq_of_lt hclt, ← hc] at hr
  simpa only [Nat.add_mod, Nat.mod_mod] using hr

theorem addMod_max_toNat (a b : UInt256) :
    (UInt256.addMod a b maxWord).toNat =
      (a.toNat + b.toNat) % (2 ^ 256 - 1) := by
  have hne : maxWord.val.val ≠ 0 := by
    change maxWord.toNat ≠ 0
    rw [maxWord_toNat]
    norm_num
  rw [UInt256.addMod, if_neg hne, word_toNat_ofNat, maxWord_toNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
    (Nat.mod_lt _ (by norm_num)) (by norm_num))

theorem pred_inverse_nat {B n p : Nat} (hB : 2 ≤ B) (hp : p < B)
    (hn : n = B - 1) (hinv : (n * p + 1) % B = 0) : p = 1 := by
  have hnp : n + 1 = B := by omega
  have he : n * p + 1 + p = B * p + 1 := by nlinarith
  have hh : (n * p + 1 + p) % B = p := by
    rw [Nat.add_mod, hinv, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hp]
  rw [he, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
    Nat.mod_eq_of_lt (by omega : 1 < B)] at hh
  simpa only [Nat.mod_eq_of_lt (by omega : 1 < B)] using hh.symm

theorem guarded_modulus_lt (n p : UInt256)
    (hinv : (n.toNat * p.toNat + 1) % 2 ^ 256 = 0)
    (hp : p ≠ UInt256.ofNat 1) : n.toNat < 2 ^ 256 - 1 := by
  have hn := word_lt_size n
  by_contra h
  have hmax : n.toNat = 2 ^ 256 - 1 := by omega
  have hv := pred_inverse_nat (by norm_num : 2 ≤ (2 : Nat) ^ 256)
    (word_lt_size p) hmax hinv
  apply hp
  apply word_ext
  simpa only [word_toNat_ofNat, show (1 : Nat) % 2 ^ 256 = 1 from by norm_num] using hv

theorem addMod_row_carry (n p t : UInt256)
    (hinv : (n.toNat * p.toNat + 1) % 2 ^ 256 = 0)
    (hp : p ≠ UInt256.ofNat 1) :
    UInt256.addMod (UInt256.mulMod n (p * t) maxWord) t maxWord =
      UInt256.isZero (UInt256.isZero (n * (p * t))) + mulHi n (p * t) := by
  apply word_ext
  rw [addMod_max_toNat, word_toNat_mulMod_max]
  have hc := c0_spec n p t hinv
  rw [Nat.mul_comm n.toNat (p * t).toNat]
  apply cancellation_nat (by norm_num) (word_lt_size (p * t))
    (guarded_modulus_lt n p hinv hp) (word_lt_size t)
  nlinarith [hc]

theorem addMod_redC (n p t : UInt256)
    (hinv : (n.toNat * p.toNat + 1) % 2 ^ 256 = 0)
    (hp : p ≠ UInt256.ofNat 1) :
    UInt256.addMod (UInt256.mulMod n (p * t) maxWord) t maxWord =
      Challenge.Modexp.Submission.Proofs.Fast.R4Math.redC n (p * t) t maxWord := by
  rw [addMod_row_carry n p t hinv hp]
  exact (row_carry_swapped n p t hinv).symm

end Challenge.Modexp.Submission.Proofs.Fast.N0Carry
