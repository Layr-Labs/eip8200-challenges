import Challenge.Modexp.Submission.Proofs.Fast.SquareProducts

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareCoefficients
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareProducts SquareWords

def dWord (mem : ByteArray) (j : Nat) : UInt256 :=
  MachineState.readWord mem (2368+32*(8-j))
def coefficient (mem : ByteArray) (ai : UInt256) (i j : Nat) : UInt256 :=
  if j = i then ai else if j = i+1 then clearBit (dWord mem j) else dWord mem j

theorem weighted_congr (f g : Nat → Nat) (i k : Nat)
    (he : ∀ j, j < k → f (i+j) = g (i+j)) : weighted f i k = weighted g i k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [weighted, weighted, ih (fun j hj => he j (by omega)), he k (by omega)]

theorem weighted_cons (f : Nat → Nat) (i k : Nat) :
    weighted f i (k+1) = f i*Limbs.radix^i + weighted f (i+1) k := by
  induction k with
  | zero => simp [weighted]
  | succ k ih =>
    rw [weighted, ih, weighted]
    have hi : i+(k+1) = (i+1)+k := by omega
    rw [hi]
    ring

theorem weighted_limbSum (f : Nat → Nat) (i k : Nat) :
    weighted f i k = limbSum (fun j => f (i+j)) k * Limbs.radix^i := by
  induction k with
  | zero => simp [weighted, limbSum]
  | succ k ih =>
    rw [weighted, limbSum_succ, ih, pow_add]
    ring

theorem weighted_digits (v i k : Nat) :
    weighted (fun j => v / Limbs.radix^j % Limbs.radix) i k =
      (v / Limbs.radix^i % Limbs.radix^k)*Limbs.radix^i := by
  rw [weighted_limbSum]
  have he : (fun j => v / Limbs.radix^(i+j) % Limbs.radix) =
      (fun j => (v / Limbs.radix^i) / Limbs.radix^j % Limbs.radix) := by
    funext j
    rw [pow_add, Nat.div_div_eq_div_mul]
  rw [he, limbSum_digits]

theorem weighted_dWords (mem : ByteArray) (v i : Nat)
    (hv : Model.FastRepresents mem 2368 9 v) (hi : i ≤ 9) :
    weighted (fun j => (dWord mem j).toNat) i (9-i) =
      (v / Limbs.radix^i)*Limbs.radix^i := by
  have he := weighted_congr (fun j => (dWord mem j).toNat)
    (fun j => v / Limbs.radix^j % Limbs.radix) i (9-i) (fun j hj =>
      Model.readLimb_of_fastRepresents (memory := mem) (ptr := 2368) (count := 9) (value := v) (k := i+j) hv (by omega))
  rw [he, weighted_digits]
  have hbound : v / Limbs.radix^i < Limbs.radix^(9-i) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos Limbs.radix_pos i), ← pow_add]
    simpa only [Nat.sub_add_cancel hi] using hv.1
  rw [Nat.mod_eq_of_lt hbound]

theorem weighted_coefficient (mem : ByteArray) (a : Nat) (ai : UInt256) (i : Nat)
    (hd : Model.FastRepresents mem 2368 9 (2*a)) (hi : i < 8) :
    weighted (fun j => (coefficient mem ai i j).toNat) i (9-i) =
      ai.toNat*Limbs.radix^i + 2*(a / Limbs.radix^(i+1))*Limbs.radix^(i+1) := by
  let c := fun j => (coefficient mem ai i j).toNat
  let d := fun j => (dWord mem j).toNat
  let P := Limbs.radix^(i+1)
  have htail : weighted c (i+2) (7-i) = weighted d (i+2) (7-i) := by
    apply weighted_congr
    intro j hj
    simp only [c, d, coefficient, if_neg (show i+2+j ≠ i by omega),
      if_neg (show i+2+j ≠ i+1 by omega)]
  have hdi : d (i+1) = (2*a/P) % Limbs.radix :=
    Model.readLimb_of_fastRepresents (memory := mem) (ptr := 2368) (count := 9) (value := 2*a) (k := i+1) hd (by omega)
  have hmod : d (i+1) % 2 = (2*a/P) % 2 := by
    rw [hdi]
    exact Nat.mod_mod_of_dvd _ (show 2 ∣ Limbs.radix by norm_num [Limbs.radix])
  have hhalf : (2*a/P)/2 = a/P := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm P 2,
      Nat.mul_div_mul_left a P (by decide)]
  have hsplit : d (i+1)%2 + 2*(a/P) = 2*a/P := by
    rw [hmod, ← hhalf]
    exact Nat.mod_add_div _ 2
  have hw := weighted_dWords mem (2*a) (i+1) hd (by omega)
  have hlen0 : 9-i = (8-i)+1 := by omega
  have hlen1 : 8-i = (7-i)+1 := by omega
  have hlen2 : 9-(i+1) = 8-i := by omega
  rw [hlen2, hlen1, weighted_cons] at hw
  have hsum : weighted c i (9-i) = ai.toNat*Limbs.radix^i +
      (d (i+1)/2*2)*P + weighted d (i+2) (7-i) := by
    rw [hlen0, weighted_cons, hlen1, weighted_cons]
    have hc0 : c i = ai.toNat := by simp [c, coefficient]
    have hc1 : c (i+1) = d (i+1)/2*2 := by
      simp only [c, coefficient, if_neg (show i+1 ≠ i by omega), ite_true,
        clearBit_toNat, d]
    rw [hc0, hc1]
    have hp : i+1+1 = i+2 := by omega
    rw [hp, htail]
    ring
  change weighted c i (9-i) = _
  rw [hsum]
  have digitSplit := Nat.mod_add_div (d (i+1)) 2
  have digitWeighted := congrArg (fun x : Nat => x*P) digitSplit
  have splitWeighted := congrArg (fun x : Nat => x*P) hsplit
  change d (i+1)*P + weighted d (i+1+1) (7-i) = (2*a/P)*P at hw
  have hp : i+1+1 = i+2 := by omega
  rw [hp] at hw
  change ai.toNat*Limbs.radix^i + (d (i+1)/2*2)*P + weighted d (i+2) (7-i) =
    ai.toNat*Limbs.radix^i + 2*(a/P)*P
  nlinarith only [hw, digitWeighted, splitWeighted]

theorem coefficient_high_le_one (mem : ByteArray) (a : Nat) (ai : UInt256) (i : Nat)
    (hd : Model.FastRepresents mem 2368 9 (2*a)) (ha : a < Limbs.radix^8) (hi : i < 8) :
    (coefficient mem ai i 8).toNat ≤ 1 := by
  have hword : (dWord mem 8).toNat = (2*a / Limbs.radix^8) % Limbs.radix :=
    Model.readLimb_of_fastRepresents (memory := mem) (ptr := 2368) (count := 9) (value := 2*a) (k := 8) hd (by decide)
  have hdiv : 2*a / Limbs.radix^8 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos Limbs.radix_pos 8)]
    omega
  have hb : (2 : Nat) < Limbs.radix := by norm_num [Limbs.radix]
  rw [Nat.mod_eq_of_lt (by omega)] at hword
  unfold coefficient
  rw [if_neg (by omega)]
  split
  · rw [clearBit_toNat, hword]
    omega
  · rw [hword]
    omega

end Challenge.Modexp.Submission.Proofs.Fast.SquareCoefficients
