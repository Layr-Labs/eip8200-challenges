import Challenge.Modexp.Submission.Proofs.CRT.WordCancellation

set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace CycleSubmission.Normalization
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.WordCancellation

theorem wrappedLowDigit (a b : Nat) (ha : a < 2^240) (hb : b ≤ 2^240) :
    (2^256 + a - b) % 2^240 =
      if a < b then a + 2^240 - b else a - b := by
  split_ifs <;> norm_num at * <;> omega

theorem digitSubtract (a n carry : UInt256)
    (ha : a.toNat < 2^240) (hn : n.toNat < 2^240) (hc : carry.toNat ≤ 1) :
    let sub := n + carry
    let borrow := UInt256.lt a sub
    let digit := UInt256.land (UInt256.ofNat (2^240-1)) (a-sub)
    digit.toNat < 2^240 ∧ borrow.toNat ≤ 1 ∧
      digit.toNat + n.toNat + carry.toNat = a.toNat + 2^240 * borrow.toNat := by
  dsimp
  have hsum : n.toNat + carry.toNat ≤ 2^240 := by omega
  have hadd : (n+carry).toNat = n.toNat + carry.toNat := by
    rw [word_toNat_add, Nat.mod_eq_of_lt]
    norm_num at hsum ⊢
    omega
  have hdigit : (UInt256.land (UInt256.ofNat (2^240-1)) (a-(n+carry))).toNat =
      if a.toNat < n.toNat + carry.toNat then a.toNat + 2^240 - (n.toNat + carry.toNat)
      else a.toNat - (n.toNat + carry.toNat) := by
    rw [land_comm]
    change ((a-(n+carry)) &&& UInt256.ofNat (2^240-1)).toNat = _
    rw [mask_toNat _ 240 (by decide), word_toNat_sub, hadd,
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 240 ≤ 256)),
        wrappedLowDigit _ _ ha hsum]
  refine ⟨?_, ?_, ?_⟩
  · change (UInt256.land (UInt256.ofNat (2^240-1)) (a-(n+carry))).toNat < 2^240
    rw [hdigit]
    split_ifs <;> omega
  · rw [word_toNat_lt, hadd]
    split_ifs <;> omega
  · change (UInt256.land (UInt256.ofNat (2^240-1)) (a-(n+carry))).toNat +
        n.toNat + carry.toNat = a.toNat + 2^240 * (UInt256.lt a (n+carry)).toNat
    rw [hdigit, word_toNat_lt, hadd]
    split_ifs <;> omega

theorem topSubtract (a n carry : UInt256)
    (hc : carry.toNat ≤ 1) (hn : n.toNat < 2^240)
    (hfinal : n.toNat + carry.toNat ≤ a.toNat) :
    (a-(n+carry)).toNat + n.toNat + carry.toNat = a.toNat ∧
      (UInt256.lt a (n+carry)).toNat = 0 := by
  have hadd : (n+carry).toNat = n.toNat + carry.toNat := by
    rw [word_toNat_add, Nat.mod_eq_of_lt]
    norm_num at hn ⊢
    omega
  have hnot : ¬ a.toNat < n.toNat + carry.toNat := by omega
  rw [word_toNat_sub_cond, word_toNat_lt, hadd, if_neg hnot]
  rw [if_neg hnot]
  omega


open HistoricalSearch.MixedMontgomery

def borrow (a n : Nat → UInt256) : Nat → UInt256
  | 0 => UInt256.ofNat 0
  | i+1 => UInt256.lt (a i) (n i + borrow a n i)

def lowDigit (a n : Nat → UInt256) (i : Nat) : UInt256 :=
  UInt256.land (UInt256.ofNat (2^240-1)) (a i - (n i + borrow a n i))

theorem borrowBound (a n : Nat → UInt256) (i : Nat) :
    (borrow a n i).toNat ≤ 1 := by
  cases i with
  | zero => change (0 : Nat) ≤ 1; omega
  | succ i =>
    simp only [borrow, word_toNat_lt]
    split_ifs <;> omega

theorem weightedSucc (B k : Nat) (f : Nat → Nat) :
    weighted B (k+1) f = weighted B k f + f k * B^k := by
  simp only [weighted, Finset.sum_range_succ]

theorem lowDigitsContract (a n : Nat → UInt256) (k : Nat)
    (ha : ∀ i < k, (a i).toNat < 2^240)
    (hn : ∀ i < k, (n i).toNat < 2^240) :
    weighted (2^240) k (fun i => (lowDigit a n i).toNat) < (2^240)^k ∧
    weighted (2^240) k (fun i => (lowDigit a n i).toNat) +
      weighted (2^240) k (fun i => (n i).toNat) =
      weighted (2^240) k (fun i => (a i).toNat) +
        (2^240)^k * (borrow a n k).toNat := by
  have hd := fun i hi => digitSubtract (a i) (n i) (borrow a n i)
    (ha i hi) (hn i hi) (borrowBound a n i)
  refine ⟨weightedBound _ _ _ (Nat.two_pow_pos _) (fun i hi => (hd i hi).1), ?_⟩
  induction k with
  | zero => simp [weighted, borrow, UInt256.toNat, UInt256.ofNat]
  | succ k ih =>
    have prev := ih (fun i hi => ha i (by omega)) (fun i hi => hn i (by omega))
      (fun i hi => hd i (by omega))
    have step := congrArg (fun x => x * (2^240)^k) (hd k (by omega)).2.2
    change ((lowDigit a n k).toNat + (n k).toNat + (borrow a n k).toNat) *
        (2^240)^k = ((a k).toNat + 2^240 * (borrow a n (k+1)).toNat) * (2^240)^k at step
    rw [weightedSucc, weightedSucc, weightedSucc, Nat.pow_succ (2^240) k]
    nlinarith

theorem topBorrowFits (q al nl ol a n b : Nat)
    (ho : ol < q) (hlow : ol + nl = al + q*b)
    (horder : nl + n*q ≤ al + a*q) : n+b ≤ a := by
  by_contra h
  have : a+1 ≤ n+b := by omega
  nlinarith [Nat.mul_le_mul_right q this]

theorem joinSubtract (q al nl ol a n b top : Nat)
    (hlow : ol + nl = al + q*b) (htop : top+n+b=a) :
    ol + top*q + (nl+n*q) = al+a*q := by
  nlinarith [congrArg (fun x => x*q) htop]

theorem nineWordSubtract (a n : Nat → UInt256)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 9, (n i).toNat < 2^240)
    (horder : weighted (2^240) 9 (fun i => (n i).toNat) ≤
      weighted (2^240) 9 (fun i => (a i).toNat)) :
    let out := weighted (2^240) 8 (fun i => (lowDigit a n i).toNat) +
      (a 8 - (n 8 + borrow a n 8)).toNat * (2^240)^8
    out + weighted (2^240) 9 (fun i => (n i).toNat) =
      weighted (2^240) 9 (fun i => (a i).toNat) ∧
      (UInt256.lt (a 8) (n 8 + borrow a n 8)).toNat = 0 := by
  have hlow := lowDigitsContract a n 8 ha (fun i hi => hn i (by omega))
  have htop : (n 8).toNat + (borrow a n 8).toNat ≤ (a 8).toNat := by
    change weighted (2^240) (8+1) _ ≤ weighted (2^240) (8+1) _ at horder
    rw [weightedSucc _ 8 (fun i => (n i).toNat),
        weightedSucc _ 8 (fun i => (a i).toNat)] at horder
    exact topBorrowFits _ _ _ _ _ _ _ hlow.1 hlow.2 horder
  have hword := topSubtract (a 8) (n 8) (borrow a n 8)
    (borrowBound a n 8) (hn 8 (by decide)) htop
  refine ⟨?_, hword.2⟩
  change _ + weighted (2^240) (8+1) _ = weighted (2^240) (8+1) _
  rw [weightedSucc _ 8 (fun i => (n i).toNat),
      weightedSucc _ 8 (fun i => (a i).toNat)]
  exact joinSubtract _ _ _ _ _ _ _ _ hlow.2 hword.1

end CycleSubmission.Normalization
