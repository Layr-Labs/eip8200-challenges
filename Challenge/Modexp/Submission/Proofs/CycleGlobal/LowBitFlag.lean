import Challenge.Modexp.Submission.Proofs.CycleGlobal.PredicateIdentity
noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.Fast.LowBitFlag
open EvmSemantics Challenge.EvmProof.Word
private theorem and_complement (n x : Nat) (hx : x < 2^n) :
    x &&& (2^n - (x+1)) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and,Nat.testBit_two_pow_sub_succ hx]
  simp only [Nat.zero_testBit]
  cases Nat.testBit x i <;> simp
private theorem isolated_pos (n x : Nat) (hx : x < 2^n) (hz : x ≠ 0) :
    0 < x &&& (2^n - x) := by
  induction n generalizing x with
  | zero => simp only [pow_zero] at hx; omega
  | succ n ih =>
    have hp : 2^(n+1) = 2 * 2^n := by simp [pow_succ,Nat.mul_comm]
    have he : 2^(n+1) % 2 = 0 := by omega
    have hh : x/2 < 2^n := by omega
    by_cases ho : x%2 = 1
    · have hn : (2^(n+1)-x)%2 = 1 := by omega
      have h := (Nat.and_mod_two_eq_one (a:=x) (b:=2^(n+1)-x)).mpr ⟨ho,hn⟩
      omega
    · have ho : x%2 = 0 := by omega
      have hq : x/2 ≠ 0 := by omega
      have hd : (2^(n+1)-x)/2 = 2^n-x/2 := by omega
      have h := ih (x/2) hh hq
      rw [← hd,← Nat.and_div_two] at h
      omega
private theorem isolate_odd (n x : Nat) (hx : x < 2^n) (ho : x%2 = 1) :
    x &&& (2^n-x) = 1 := by
  cases n with
  | zero => simp only [pow_zero] at hx; omega
  | succ n =>
    have hp : 2^(n+1) = 2 * 2^n := by simp [pow_succ,Nat.mul_comm]
    have hn : (2^(n+1)-x)%2 = 1 := by omega
    have hd : (2^(n+1)-x)/2 = 2^n-(x/2+1) := by omega
    have hc := and_complement n (x/2) (by omega)
    have hq : (x &&& (2^(n+1)-x))/2 = 0 := by
      rw [Nat.and_div_two,hd]; exact hc
    have hm := (Nat.and_mod_two_eq_one (a:=x) (b:=2^(n+1)-x)).mpr ⟨ho,hn⟩
    omega
private theorem isolate_small (n x : Nat) (hx : x < 2^n) :
    x &&& ((2^n-x)%2^n) < 2 ↔ x = 0 ∨ x%2 = 1 := by
  by_cases hz : x = 0
  · simp [hz]
  · have hpos := isolated_pos n x hx hz
    have hm : (2^n-x)%2^n = 2^n-x := Nat.mod_eq_of_lt (by omega)
    rw [hm]
    by_cases ho : x%2 = 1
    · rw [isolate_odd n x hx ho]; simp [ho]
    · have he : (x &&& (2^n-x))%2 = 0 := by
        have hn := Nat.and_mod_two_eq_one (a:=x) (b:=2^n-x)
        omega
      constructor <;> intro h <;> omega
/-- Universal word predicate, proved with kernel-checked natural-number induction. -/
theorem flag (a : UInt256) :
    UInt256.gt (UInt256.ofNat 2)
      (UInt256.land (UInt256.ofNat 0 - a) a) =
    UInt256.lor (UInt256.land (UInt256.ofNat 1) a) (UInt256.isZero a) := by
  apply word_ext
  have h := isolate_small 256 a.toNat a.val.isLt
  have hz : (UInt256.ofNat 0 - a).toNat = (2^256-a.toNat)%2^256 := by
    rw [word_toNat_sub]; norm_num
  have hg : (UInt256.gt (UInt256.ofNat 2)
      (UInt256.land (UInt256.ofNat 0 - a) a)).toNat =
      if a.toNat &&& ((2^256-a.toNat)%2^256) < 2 then 1 else 0 := by
    unfold UInt256.gt
    have hc : (UInt256.ofNat 2).toNat = 2 := by decide
    rw [hc,word_toNat_land,hz,Nat.and_comm]
    split <;> rfl
  rw [hg,word_toNat_lor,word_toNat_land,word_toNat_isZero]
  have hone : (UInt256.ofNat 1).toNat = 1 := by decide
  rw [hone,Nat.one_and_eq_mod_two]
  by_cases ha : a.toNat = 0
  · simp [ha]
  · by_cases ho : a.toNat%2 = 1
    · have hh := h.mpr (Or.inr ho)
      simp only [hh,ha,ho,if_true,if_false]
      decide
    · have hh : ¬ a.toNat &&& ((2^256-a.toNat)%2^256) < 2 := by
        rw [h]; simp [ha,ho]
      have hp : a.toNat%2 = 0 := by omega
      simp only [hh,ha,hp,if_false]
      decide
theorem flagRaw (a : UInt256) :
    UInt256.gt (UInt256.ofNat 2)
      (UInt256.land (({val := 0} : UInt256) - a) a) =
    UInt256.lor (UInt256.land (UInt256.ofNat 1) a) (UInt256.isZero a) := flag a
#print axioms flag
end CycleSubmission.Global.Fast.LowBitFlag
