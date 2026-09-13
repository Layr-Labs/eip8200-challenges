import Challenge.Modexp.Submission.Proofs.Fast.R4Math
import Challenge.Modexp.Submission.Proofs.Fast.SquareMath
import Challenge.Modexp.Submission.Proofs.Fast.SquareDiag

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# R4：五字累加窗口的数值不变式

`val5 W = t0 + t1·R + t2·R² + t3·R³ + t4·R⁴`。每个积行把行贡献 `rowX r` 加进窗口
（溢出位记在 `R⁵`），每次约化把窗口加上 `mu · M` 再整体除以 `R`。四行之后
`val5 final · R⁴ = A² + Q · M`，`Q < R⁴`，与旧 `sq_row` 模型的 `sqRows_invariant` 同形。
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Value

open EvmSemantics
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro R4Math

/-- 五字窗口的数值（`t4` 最高）。 -/
def val5 (W : W5) : Nat :=
  W.t0.toNat + W.t1.toNat * 2 ^ 256 + W.t2.toNat * (2 ^ 256) ^ 2 + W.t3.toNat * (2 ^ 256) ^ 3 +
    W.t4.toNat * (2 ^ 256) ^ 4

theorem push0_eq : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide

/-- `SGT 0 p` 的数值是 `p` 的最高位。 -/
theorem tb_toNat (p : UInt256) : (UInt256.sgt ⟨0⟩ p).toNat = p.toNat / 2 ^ 255 := by
  rw [push0_eq]; exact SquareDiag.sgt_zero_toNat p

theorem tb_le_one (p : UInt256) : (UInt256.sgt ⟨0⟩ p).toNat ≤ 1 := by
  rw [tb_toNat]
  have := toNat_lt p
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega))

/-- 乘以一个比特不回绕。 -/
theorem mul_bit (a b : UInt256) (hb : b.toNat ≤ 1) : (a * b).toNat = a.toNat * b.toNat := by
  rw [toNat_mul]
  apply Nat.mod_eq_of_lt
  have := toNat_lt a
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h <;> rw [h] <;> omega

theorem lt_le_one (a b : UInt256) : (UInt256.lt a b).toNat ≤ 1 := by
  rw [toNat_ltw]; split <;> omega

/-- 行乘数 `(a + a) + tb` 的数值。 -/
theorem dbl_toNat (a tb : UInt256) :
    ((a + a) + tb).toNat = (2 * a.toNat + tb.toNat) % 2 ^ 256 := by
  rw [word_toNat_add, word_toNat_add, Nat.mod_add_mod]
  congr 1; ring

/-! ## 行与约化的数值方程（`k = maxWord`） -/

theorem row0_val (a0 a1 a2 a3 : UInt256) :
    val5 (row0 a0 a1 a2 a3 maxWord) =
      a0.toNat * a0.toNat +
        (a0 + a0).toNat * (a1.toNat * 2 ^ 256 + a2.toNat * (2 ^ 256) ^ 2 + a3.toNat * (2 ^ 256) ^ 3) := by
  have h0 := dHi_spec a0
  have h1 := zCell_spec a1 (a0 + a0) (dHi a0 maxWord)
  have h2 := zCell_spec a2 (a0 + a0) (zCarry a1 (a0 + a0) (dHi a0 maxWord) maxWord)
  have h3 := zCell_spec a3 (a0 + a0)
    (zCarry a2 (a0 + a0) (zCarry a1 (a0 + a0) (dHi a0 maxWord) maxWord) maxWord)
  simp only [val5, row0]
  zify at h0 h1 h2 h3 ⊢
  linear_combination h0 + 2 ^ 256 * h1 + (2 ^ 256) ^ 2 * h2 + (2 ^ 256) ^ 3 * h3

theorem row1_val (a0 a1 a2 a3 : UInt256) (P : W5) :
    val5 (row1 a0 a1 a2 a3 maxWord P).1 + (row1 a0 a1 a2 a3 maxWord P).2.toNat * (2 ^ 256) ^ 5 =
      val5 P + a1.toNat * (a1.toNat + (UInt256.sgt ⟨0⟩ a0).toNat) * 2 ^ 256 +
        ((a1 + a1) + UInt256.sgt ⟨0⟩ a0).toNat *
          (a2.toNat * (2 ^ 256) ^ 2 + a3.toNat * (2 ^ 256) ^ 3) := by
  have hb := mul_bit a1 (UInt256.sgt ⟨0⟩ a0) (tb_le_one a0)
  simp only [row1]
  generalize UInt256.sgt ⟨0⟩ a0 = tb at hb ⊢
  have h1 := mCell_spec a1 a1 (a1 * tb) P.t1
  have h2 := mCell_spec a2 ((a1 + a1) + tb) (mCarry a1 a1 (a1 * tb) P.t1 maxWord) P.t2
  have h3 := mCell_spec a3 ((a1 + a1) + tb)
    (mCarry a2 ((a1 + a1) + tb) (mCarry a1 a1 (a1 * tb) P.t1 maxWord) P.t2 maxWord) P.t3
  have h4 := add_spec P.t4 (mCarry a3 ((a1 + a1) + tb)
    (mCarry a2 ((a1 + a1) + tb) (mCarry a1 a1 (a1 * tb) P.t1 maxWord) P.t2 maxWord) P.t3 maxWord)
  simp only [val5]
  rw [hb] at h1
  zify at h1 h2 h3 h4 ⊢
  linear_combination 2 ^ 256 * h1 + (2 ^ 256) ^ 2 * h2 + (2 ^ 256) ^ 3 * h3 + (2 ^ 256) ^ 4 * h4

theorem row2_val (a1 a2 a3 : UInt256) (P : W5) :
    val5 (row2 a1 a2 a3 maxWord P).1 + (row2 a1 a2 a3 maxWord P).2.toNat * (2 ^ 256) ^ 5 =
      val5 P + a2.toNat * (a2.toNat + (UInt256.sgt ⟨0⟩ a1).toNat) * (2 ^ 256) ^ 2 +
        ((a2 + a2) + UInt256.sgt ⟨0⟩ a1).toNat * (a3.toNat * (2 ^ 256) ^ 3) := by
  have hb := mul_bit a2 (UInt256.sgt ⟨0⟩ a1) (tb_le_one a1)
  simp only [row2]
  generalize UInt256.sgt ⟨0⟩ a1 = tb at hb ⊢
  have h2 := mCell_spec a2 a2 (a2 * tb) P.t2
  have h3 := mCell_spec a3 ((a2 + a2) + tb) (mCarry a2 a2 (a2 * tb) P.t2 maxWord) P.t3
  have h4 := add_spec P.t4 (mCarry a3 ((a2 + a2) + tb) (mCarry a2 a2 (a2 * tb) P.t2 maxWord) P.t3 maxWord)
  simp only [val5]
  rw [hb] at h2
  zify at h2 h3 h4 ⊢
  linear_combination (2 ^ 256) ^ 2 * h2 + (2 ^ 256) ^ 3 * h3 + (2 ^ 256) ^ 4 * h4

theorem row3_val (a2 a3 : UInt256) (P : W5) :
    val5 (row3 a2 a3 maxWord P).1 + (row3 a2 a3 maxWord P).2.toNat * (2 ^ 256) ^ 5 =
      val5 P + a3.toNat * (a3.toNat + (UInt256.sgt ⟨0⟩ a2).toNat) * (2 ^ 256) ^ 3 := by
  have hb := mul_bit a3 (UInt256.sgt ⟨0⟩ a2) (tb_le_one a2)
  simp only [row3]
  generalize UInt256.sgt ⟨0⟩ a2 = tb at hb ⊢
  have h3 := mCell_spec a3 a3 (a3 * tb) P.t3
  have h4 := add_spec P.t4 (mCarry a3 a3 (a3 * tb) P.t3 maxWord)
  simp only [val5]
  rw [hb] at h3
  zify at h3 h4 ⊢
  linear_combination (2 ^ 256) ^ 3 * h3 + (2 ^ 256) ^ 4 * h4

theorem red_val (n0 n1 n2 n3 np : UInt256) (P : W5) (v : UInt256) (hv : v.toNat ≤ 1)
    (hinv : (n0.toNat * np.toNat + 1) % 2 ^ 256 = 0) :
    val5 (red n0 n1 n2 n3 np maxWord P v) * 2 ^ 256 =
      val5 P + v.toNat * (2 ^ 256) ^ 5 +
        (np * P.t0).toNat * (n0.toNat + n1.toNat * 2 ^ 256 + n2.toNat * (2 ^ 256) ^ 2 +
          n3.toNat * (2 ^ 256) ^ 3) := by
  simp only [red]
  generalize hm : np * P.t0 = m
  have h0 := redC_spec n0 np P.t0 hinv
  rw [hm] at h0
  have h1 := sCell_spec n1 m (redC n0 m P.t0 maxWord) P.t1
  have h2 := sCell_spec n2 m (sCarry n1 m (redC n0 m P.t0 maxWord) P.t1 maxWord) P.t2
  have h3 := sCell_spec n3 m
    (sCarry n2 m (sCarry n1 m (redC n0 m P.t0 maxWord) P.t1 maxWord) P.t2 maxWord) P.t3
  generalize sCarry n3 m (sCarry n2 m (sCarry n1 m (redC n0 m P.t0 maxWord) P.t1 maxWord) P.t2
    maxWord) P.t3 maxWord = c3 at h3 ⊢
  have h4 := add_spec P.t4 c3
  have hvo : (v + UInt256.lt (P.t4 + c3) P.t4).toNat = v.toNat + (UInt256.lt (P.t4 + c3) P.t4).toNat := by
    rw [word_toNat_add]
    apply Nat.mod_eq_of_lt
    have := lt_le_one (P.t4 + c3) P.t4
    omega
  simp only [val5, hvo]
  zify at h0 h1 h2 h3 h4 ⊢
  linear_combination h0 + 2 ^ 256 * h1 + (2 ^ 256) ^ 2 * h2 + (2 ^ 256) ^ 3 * h3 +
    (2 ^ 256) ^ 4 * h4

/-! ## 四行合成 -/

/-- `a` 的四个 limb（`a0` 最低）。 -/
def limbs4 (a0 a1 a2 a3 : UInt256) : Nat → Nat
  | 0 => a0.toNat
  | 1 => a1.toNat
  | 2 => a2.toNat
  | 3 => a3.toNat
  | _ => 0

private theorem bound_step {B x y k : Nat} (_hB : 0 < B) (hx : x < B) (hy : y < B ^ k) :
    x + B * y < B ^ (k + 1) := by
  have h1 : y + 1 ≤ B ^ k := hy
  have h2 : B * (y + 1) ≤ B * B ^ k := Nat.mul_le_mul_left B h1
  rw [Nat.mul_add, Nat.mul_one] at h2
  rw [pow_succ, Nat.mul_comm (B ^ k) B]
  linarith

/-- 四行贡献之和（`h` 保持符号，避免字面量化简干扰差式匹配）。 -/
private theorem rowX_sum4 (h : Nat) (f : Nat → Nat) :
    SquareMath.lsum (2 * h) (SquareMath.rowX h 4 f) 4 =
      (f 0 * (f 0 + SquareMath.tbm h f 0) + SquareMath.a2 h f 0 *
          (f 1 * (2 * h) + f 2 * (2 * h) ^ 2 + f 3 * (2 * h) ^ 3)) +
        (f 1 * (f 1 + SquareMath.tbm h f 1) * (2 * h) + SquareMath.a2 h f 1 *
          (f 2 * (2 * h) ^ 2 + f 3 * (2 * h) ^ 3)) * (2 * h) +
        (f 2 * (f 2 + SquareMath.tbm h f 2) * (2 * h) ^ 2 + SquareMath.a2 h f 2 *
          (f 3 * (2 * h) ^ 3)) * (2 * h) ^ 2 +
        (f 3 * (f 3 + SquareMath.tbm h f 3) * (2 * h) ^ 3) * (2 * h) ^ 3 := by
  have e4 : ∀ g : Nat → Nat, SquareMath.lsum (2 * h) g 4 =
      g 0 + g 1 * (2 * h) + g 2 * (2 * h) ^ 2 + g 3 * (2 * h) ^ 3 := by
    intro g; simp only [SquareMath.lsum]; ring
  have s1 : SquareMath.lsum (2 * h) f 4 - SquareMath.lsum (2 * h) f 1 =
      f 1 * (2 * h) + f 2 * (2 * h) ^ 2 + f 3 * (2 * h) ^ 3 :=
    Nat.sub_eq_of_eq_add (by rw [e4 f]; simp only [SquareMath.lsum]; ring)
  have s2 : SquareMath.lsum (2 * h) f 4 - SquareMath.lsum (2 * h) f 2 =
      f 2 * (2 * h) ^ 2 + f 3 * (2 * h) ^ 3 :=
    Nat.sub_eq_of_eq_add (by rw [e4 f]; simp only [SquareMath.lsum]; ring)
  have s3 : SquareMath.lsum (2 * h) f 4 - SquareMath.lsum (2 * h) f 3 =
      f 3 * (2 * h) ^ 3 :=
    Nat.sub_eq_of_eq_add (by rw [e4 f]; simp only [SquareMath.lsum]; ring)
  rw [e4 (SquareMath.rowX h 4 f)]
  simp only [SquareMath.rowX, s1, s2, s3, Nat.sub_self]
  ring

set_option maxHeartbeats 8000000 in
/-- 合成的核心：中间窗口作为变量（避免展开 `final` 造成的项膨胀）。 -/
theorem final_eq_aux (a0 a1 a2 a3 n0 n1 n2 n3 np : UInt256) (W1 W2 W3 : W5)
    (R1 R2 R3 : W5 × UInt256)
    (hW1 : W1 = red n0 n1 n2 n3 np maxWord (row0 a0 a1 a2 a3 maxWord) ⟨0⟩)
    (hR1 : R1 = row1 a0 a1 a2 a3 maxWord W1)
    (hW2 : W2 = red n0 n1 n2 n3 np maxWord R1.1 R1.2)
    (hR2 : R2 = row2 a1 a2 a3 maxWord W2)
    (hW3 : W3 = red n0 n1 n2 n3 np maxWord R2.1 R2.2)
    (hR3 : R3 = row3 a2 a3 maxWord W3)
    (hinv : (n0.toNat * np.toNat + 1) % 2 ^ 256 = 0) :
    ∃ Q, Q < (2 ^ 256) ^ 4 ∧
      val5 (red n0 n1 n2 n3 np maxWord R3.1 R3.2) * (2 ^ 256) ^ 4 =
        SquareMath.lsum (2 * 2 ^ 255) (limbs4 a0 a1 a2 a3) 4 ^ 2 +
          Q * (n0.toNat + n1.toNat * 2 ^ 256 + n2.toNat * (2 ^ 256) ^ 2 +
            n3.toNat * (2 ^ 256) ^ 3) := by
  have hB : (2 : Nat) * 2 ^ 255 = 2 ^ 256 := by norm_num
  have hlimb : ∀ k, limbs4 a0 a1 a2 a3 k < 2 * 2 ^ 255 := by
    intro k; rw [hB]
    match k with
    | 0 => exact toNat_lt a0
    | 1 => exact toNat_lt a1
    | 2 => exact toNat_lt a2
    | 3 => exact toNat_lt a3
    | _ + 4 => simp [limbs4]
  have hsq := SquareMath.square_identity (h := 2 ^ 255) (by norm_num) (limbs4 a0 a1 a2 a3) hlimb 4
  have e0 := red_val n0 n1 n2 n3 np (row0 a0 a1 a2 a3 maxWord) ⟨0⟩ (by decide) hinv
  have e1 := red_val n0 n1 n2 n3 np R1.1 R1.2 (by rw [hR1]; exact lt_le_one _ _) hinv
  have e2 := red_val n0 n1 n2 n3 np R2.1 R2.2 (by rw [hR2]; exact lt_le_one _ _) hinv
  have e3 := red_val n0 n1 n2 n3 np R3.1 R3.2 (by rw [hR3]; exact lt_le_one _ _) hinv
  have f0 := row0_val a0 a1 a2 a3
  have f1 := row1_val a0 a1 a2 a3 W1
  have f2 := row2_val a1 a2 a3 W2
  have f3 := row3_val a2 a3 W3
  rw [← hW1] at e0
  rw [← hR1] at f1
  rw [← hW2] at e1
  rw [← hR2] at f2
  rw [← hW3] at e2
  rw [← hR3] at f3
  have htb1 := tb_toNat a0
  have htb2 := tb_toNat a1
  have htb3 := tb_toNat a2
  have hd0 : (a0 + a0).toNat = (2 * a0.toNat + 0) % 2 ^ 256 := by
    rw [word_toNat_add, Nat.add_zero, Nat.two_mul]
  have hd1 := dbl_toNat a1 (UInt256.sgt ⟨0⟩ a0)
  have hd2 := dbl_toNat a2 (UInt256.sgt ⟨0⟩ a1)
  have hz : (⟨0⟩ : UInt256).toNat = 0 := rfl
  refine ⟨(np * (row0 a0 a1 a2 a3 maxWord).t0).toNat + 2 ^ 256 * ((np * R1.1.t0).toNat +
    2 ^ 256 * ((np * R2.1.t0).toNat + 2 ^ 256 * (np * R3.1.t0).toNat)), ?_, ?_⟩
  · have hpos : 0 < 2 ^ 256 := by norm_num
    have b3 : (np * R3.1.t0).toNat < (2 ^ 256) ^ 1 := by simpa using toNat_lt (np * R3.1.t0)
    have b2 := bound_step hpos (toNat_lt (np * R2.1.t0)) b3
    have b1 := bound_step hpos (toNat_lt (np * R1.1.t0)) b2
    exact bound_step hpos (toNat_lt (np * (row0 a0 a1 a2 a3 maxWord).t0)) b1
  · have hX : SquareMath.lsum (2 * 2 ^ 255) (SquareMath.rowX (2 ^ 255) 4 (limbs4 a0 a1 a2 a3)) 4 =
        (a0.toNat * a0.toNat + (a0 + a0).toNat *
            (a1.toNat * 2 ^ 256 + a2.toNat * (2 ^ 256) ^ 2 + a3.toNat * (2 ^ 256) ^ 3)) +
          (a1.toNat * (a1.toNat + (UInt256.sgt ⟨0⟩ a0).toNat) * 2 ^ 256 +
            ((a1 + a1) + UInt256.sgt ⟨0⟩ a0).toNat *
              (a2.toNat * (2 ^ 256) ^ 2 + a3.toNat * (2 ^ 256) ^ 3)) * 2 ^ 256 +
          (a2.toNat * (a2.toNat + (UInt256.sgt ⟨0⟩ a1).toNat) * (2 ^ 256) ^ 2 +
            ((a2 + a2) + UInt256.sgt ⟨0⟩ a1).toNat * (a3.toNat * (2 ^ 256) ^ 3)) * (2 ^ 256) ^ 2 +
          (a3.toNat * (a3.toNat + (UInt256.sgt ⟨0⟩ a2).toNat) * (2 ^ 256) ^ 3) * (2 ^ 256) ^ 3 := by
      rw [rowX_sum4]
      simp only [SquareMath.a2, SquareMath.tbm, limbs4, hd0, hd1, hd2, htb1, htb2, htb3]
      ring_nf
    rw [← hsq, hX]
    rw [hz] at e0
    rw [f0] at e0
    zify at e0 e1 e2 e3 f1 f2 f3 ⊢
    linear_combination (2 ^ 256) ^ 3 * e3 + (2 ^ 256) ^ 3 * f3 + (2 ^ 256) ^ 2 * e2 +
      (2 ^ 256) ^ 2 * f2 + 2 ^ 256 * e1 + 2 ^ 256 * f1 + e0

/-- **R4 的数值结论**：`val5 final · R⁴ = A² + Q · M`，`Q < R⁴`。 -/
theorem final_eq (a0 a1 a2 a3 n0 n1 n2 n3 np : UInt256)
    (hinv : (n0.toNat * np.toNat + 1) % 2 ^ 256 = 0) :
    ∃ Q, Q < (2 ^ 256) ^ 4 ∧
      val5 (final a0 a1 a2 a3 n0 n1 n2 n3 np maxWord) * (2 ^ 256) ^ 4 =
        SquareMath.lsum (2 * 2 ^ 255) (limbs4 a0 a1 a2 a3) 4 ^ 2 +
          Q * (n0.toNat + n1.toNat * 2 ^ 256 + n2.toNat * (2 ^ 256) ^ 2 +
            n3.toNat * (2 ^ 256) ^ 3) :=
  final_eq_aux a0 a1 a2 a3 n0 n1 n2 n3 np _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl hinv

end Challenge.Modexp.Submission.Proofs.Fast.R4Value
