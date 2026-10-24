import Challenge.Modexp.Submission.Proofs.Cycle.ColumnWords
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace CycleSubmission.KernelContract
open EvmSemantics
open HistoricalSearch.MixedMontgomery
open CycleSubmission.WordArithmetic CycleSubmission.ColumnWords

structure Trace (k : Kernel) (inv : UInt256) (a b n : Nat → UInt256) where
  q : Nat → UInt256
  c : Nat → UInt256
  d : Nat → UInt256
  zero : (c 0).toNat = 0
  quotient : ∀ i < 9, q i = quotientWord k i (c i) inv a b n q
  carry : ∀ i < 17, c (i+1) = carryWord k i (c i) inv a b n q
  digit : ∀ i, 9 ≤ i → i < 17 → d (i-9) = digitWord k i (c i) inv a b n q
  top : d 8 = c 17

namespace Trace
variable {k : Kernel} {inv : UInt256} {a b n : Nat → UInt256}
variable (t : Trace k inv a b n)

theorem q_bound : ∀ i < 9, (t.q i).toNat < radix := by
  intro i hi
  rw [t.quotient i hi]
  exact quotient_bound k i hi (t.c i) inv a b n t.q

theorem c_bound
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hinv : (N*inv.toNat+1) % 2^256 = 0) :
    ∀ i ≤ 17, (t.c i).toNat ≤ 18*(radix-1) := by
  intro i hi
  induction i with
  | zero => rw [t.zero]; exact Nat.zero_le _
  | succ i ih =>
    have hc := ih (by omega)
    have h := contract k i (by omega) (t.c i) inv a b n t.q
      ha hb hn t.q_bound hc N hn0 hinv (t.quotient i)
    rw [t.carry i (by omega), h.1]
    exact (CycleSubmission.Bounds.fullColumnBounds _ _ hc
      (value_bound k i (by omega) (t.c i) inv a b n t.q ha hb hn t.q_bound hc)).1

def digits (i : Nat) : Nat := if i < 9 then 0 else (t.d (i-9)).toNat
def carries (i : Nat) : Nat := if i = 18 then 0 else (t.c i).toNat

theorem recurrence
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hinv : (N*inv.toNat+1) % 2^256 = 0) :
    ∀ i < 18, t.digits i + radix*t.carries (i+1) =
      convolution 9 (fun j => (a j).toNat) (fun j => (other k a b j).toNat) i +
      convolution 9 (fun j => (t.q j).toNat) (fun j => (n j).toNat) i + t.carries i := by
  intro i hi
  by_cases hf : i = 17
  · subst i
    simp only [digits, carries, show ¬ (17 < 9) by decide, if_false,
      show 17-9 = 8 from rfl, show 17+1 = 18 from rfl, ite_true,
      show ¬ (17 = 18) by decide, Nat.mul_zero, Nat.add_zero,
      CycleSubmission.Convolution.column17, Nat.zero_add, t.top]
  · have hi17 : i < 17 := by omega
    have hc := t.c_bound ha hb hn N hn0 hinv i (by omega)
    have h := contract k i hi17 (t.c i) inv a b n t.q
      ha hb hn t.q_bound hc N hn0 hinv (t.quotient i)
    have hv := value_convolution k i hi17 (t.c i) inv a b n t.q
      (by intro hz; subst i; exact t.zero)
    have hd := Nat.mod_add_div (high k i (t.c i) inv a b n t.q).value radix
    rw [← h.1, ← t.carry i hi17] at hd
    simp only [carries, show i+1 ≠ 18 by omega, show i ≠ 18 by omega, if_false]
    rw [hv] at hd
    by_cases he : i < 9
    · have hz : (high k i (t.c i) inv a b n t.q).value % radix = 0 := by
        simpa only [if_pos he] using h.2
      rw [hv] at hz
      rw [hz] at hd
      simpa only [digits, if_pos he, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd
    · have hz : (t.d (i-9)).toNat =
          (high k i (t.c i) inv a b n t.q).value % radix := by
        rw [t.digit i (by omega) hi17]
        exact (show (digitWord k i (t.c i) inv a b n t.q).toNat = _ from
          by simpa only [if_neg he] using h.2)
      rw [hv] at hz
      rw [← hz] at hd
      simpa only [digits, if_neg he, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd

theorem exact_product
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hinv : (N*inv.toNat+1) % 2^256 = 0) :
    weighted radix 9 (fun i => (t.d i).toNat) * radix^9 =
      weighted radix 9 (fun i => (a i).toNat) *
      weighted radix 9 (fun i => (other k a b i).toNat) +
      weighted radix 9 (fun i => (t.q i).toNat) * weighted radix 9 (fun i => (n i).toNat) := by
  have h := CycleSubmission.Radix.alignedExact radix
    (fun i => (a i).toNat) (fun i => (other k a b i).toNat)
    (fun i => (t.q i).toNat) (fun i => (n i).toNat) t.digits t.carries
    (by simpa only [carries, show ¬ (0 = 18) by decide, if_false] using t.zero)
    (by rfl)
    (by intro i hi; simp only [digits, if_pos hi])
    (t.recurrence ha hb hn N hn0 hinv)
  have hd : (fun i => t.digits (9+i)) = (fun i => (t.d i).toNat) := by
    funext i
    simp only [digits, show ¬ (9+i < 9) by omega, if_false, Nat.add_sub_cancel_left]
  rw [hd] at h
  exact h

theorem output_low_bound
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hinv : (N*inv.toNat+1) % 2^256 = 0) :
    ∀ i < 8, (t.d i).toNat < radix := by
  intro i hi
  have hc := t.c_bound ha hb hn N hn0 hinv (i+9) (by omega)
  have h := contract k (i+9) (by omega) (t.c (i+9)) inv a b n t.q
    ha hb hn t.q_bound hc N hn0 hinv (t.quotient (i+9))
  have hd := t.digit (i+9) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hd
  rw [hd]
  have he : ¬ (i+9 < 9) := by omega
  have hz := h.2
  simp only [if_neg he] at hz
  rw [hz]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem normalized_contract
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hNvalue : weighted radix 9 (fun i => (n i).toNat) = N)
    (hinv : (N*inv.toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hNR : N < radix^9) (hodd : Odd N) :
    let T := weighted radix 9 (fun i => (t.d i).toNat)
    T < radix^9+N ∧
    normalize (radix^9) N T < radix^9 ∧
    normalize (radix^9) N T % N =
      Challenge.Modexp.Submission.Proofs.Fast.Model.montMul N (radix^9)
        (weighted radix 9 (fun i => (a i).toNat))
        (weighted radix 9 (fun i => (other k a b i).toNat)) := by
  dsimp only
  have hr : 0 < radix^9 := Nat.pow_pos (Nat.two_pow_pos _) 
  have hA := weightedBound radix 9 (fun i => (a i).toNat) (Nat.two_pow_pos _) ha
  have hB : weighted radix 9 (fun i => (other k a b i).toNat) < radix^9 := by
    apply weightedBound radix 9 _ (Nat.two_pow_pos _)
    cases k
    · exact ha
    · exact hb
  have hQ := weightedBound radix 9 (fun i => (t.q i).toNat) (Nat.two_pow_pos _) t.q_bound
  have he := t.exact_product ha hb hn N hn0 hinv
  rw [hNvalue] at he
  have ht : weighted radix 9 (fun i => (t.d i).toNat) =
      (weighted radix 9 (fun i => (a i).toNat) *
       weighted radix 9 (fun i => (other k a b i).toNat) +
       weighted radix 9 (fun i => (t.q i).toNat)*N) / radix^9 := by
    rw [← he, Nat.mul_div_cancel _ hr]
  refine ⟨?_, arithmeticContract _ _ _ _ _ _ hr hN hNR hA hB hQ
    (CycleSubmission.Radix.oddCoprime 240 N hodd) he⟩
  rw [ht]
  exact montgomeryRange _ _ _ _ _ hr hN hA hB hQ

end Trace
end CycleSubmission.KernelContract
