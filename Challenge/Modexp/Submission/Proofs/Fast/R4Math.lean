import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# R4：4-limb 平方例程的字级模型

R4 把 4-limb 平方的累加行 `t` 常驻栈上，按行展开；约化行是共享子程序。本文件
只放与字节码逐字一致的字级公式（每个定义就是对应指令序列算出的表达式，运算数顺序
与栈上弹出顺序一致），不引用任何 pc 或内存布局。

记号：`o` 源 limb，`d` 行乘数，`c` 进位，`t` 原累加 limb，`k = 2^256 - 1`
（`MULMOD` 的模数，栈上的 `allOnes`）。
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Math

open EvmSemantics

/-- 累加 limb 为零时的格：存 `c + lo`。 -/
def zSum (o d c : UInt256) : UInt256 := c + o * d

/-- 累加 limb 为零时的格的进位：`hi + [c + lo 溢出]`，高字经 `MULMOD k` 求出。 -/
def zCarry (o d c k : UInt256) : UInt256 :=
  (UInt256.gt c (c + o * d) - (UInt256.gt (o * d) (UInt256.mulMod d o k) - UInt256.mulMod d o k)) -
    o * d

/-- 行 0 对角格的高字：`a * a` 的高 256 位。 -/
def dHi (a k : UInt256) : UInt256 :=
  (⟨0⟩ : UInt256) - (a * a + (UInt256.gt (a * a) (UInt256.mulMod a a k) - UInt256.mulMod a a k))

/-- 一般格：存 `(c + lo) + t`。 -/
def mSum (o d c t : UInt256) : UInt256 := (c + o * d) + t

/-- 一般格（积行）的进位：第二个溢出位用 `LT(s, t)`。 -/
def mCarry (o d c t k : UInt256) : UInt256 :=
  zCarry o d c k + UInt256.lt (mSum o d c t) t

/-- 约化格的进位：第二个溢出位用 `GT(x, s)`（`x = c + lo`）。 -/
def sCarry (o d c t k : UInt256) : UInt256 :=
  zCarry o d c k + UInt256.gt (zSum o d c) (mSum o d c t)

/-- 约化首格（`m = np * t0`）的进位：`y = t0 + MULMOD(n0, m, k)`，`c = [t0 > y] + y`。 -/
def redC (n0 m t0 k : UInt256) : UInt256 :=
  UInt256.gt t0 (t0 + UInt256.mulMod n0 m k) + (t0 + UInt256.mulMod n0 m k)


/-! ## 行模型

`W5` 是栈上的五个累加字 `t0..t4`（`t4` 为最高字）。`row0` 是累加区为零的行 0；
`row1..row3` 是积行（对角格 + 交叉格 + `t4` 吸收进位，返回溢出位 `v`）；`red` 是共享的
约化子程序（`m = np * t0`，结果整体下移一个 limb）。 -/

structure W5 where
  t0 : UInt256
  t1 : UInt256
  t2 : UInt256
  t3 : UInt256
  t4 : UInt256

/-- 行 0：`t = a0 * a`（累加区为零，`d = a0 + a0`）。 -/
def row0 (a0 a1 a2 a3 k : UInt256) : W5 :=
  let d := a0 + a0
  let c0 := dHi a0 k
  let c1 := zCarry a1 d c0 k
  let c2 := zCarry a2 d c1 k
  { t0 := a0 * a0, t1 := zSum a1 d c0, t2 := zSum a2 d c1, t3 := zSum a3 d c2,
    t4 := zCarry a3 d c2 k }

/-- 积行 1：`tb = SGT 0 a0`，对角格进位入口 `a1 * tb`，交叉乘数 `(a1 + a1) + tb`。 -/
def row1 (a0 a1 a2 a3 k : UInt256) (P : W5) : W5 × UInt256 :=
  let tb := UInt256.sgt ⟨0⟩ a0
  let d := (a1 + a1) + tb
  let c1 := mCarry a1 a1 (a1 * tb) P.t1 k
  let c2 := mCarry a2 d c1 P.t2 k
  let c3 := mCarry a3 d c2 P.t3 k
  ({ t0 := P.t0, t1 := mSum a1 a1 (a1 * tb) P.t1, t2 := mSum a2 d c1 P.t2,
     t3 := mSum a3 d c2 P.t3, t4 := P.t4 + c3 },
   UInt256.lt (P.t4 + c3) P.t4)

/-- 积行 2。 -/
def row2 (a1 a2 a3 k : UInt256) (P : W5) : W5 × UInt256 :=
  let tb := UInt256.sgt ⟨0⟩ a1
  let d := (a2 + a2) + tb
  let c2 := mCarry a2 a2 (a2 * tb) P.t2 k
  let c3 := mCarry a3 d c2 P.t3 k
  ({ t0 := P.t0, t1 := P.t1, t2 := mSum a2 a2 (a2 * tb) P.t2, t3 := mSum a3 d c2 P.t3,
     t4 := P.t4 + c3 },
   UInt256.lt (P.t4 + c3) P.t4)

/-- 积行 3（只有对角格）。 -/
def row3 (a2 a3 k : UInt256) (P : W5) : W5 × UInt256 :=
  let tb := UInt256.sgt ⟨0⟩ a2
  let c3 := mCarry a3 a3 (a3 * tb) P.t3 k
  ({ t0 := P.t0, t1 := P.t1, t2 := P.t2, t3 := mSum a3 a3 (a3 * tb) P.t3, t4 := P.t4 + c3 },
   UInt256.lt (P.t4 + c3) P.t4)

/-- 约化子程序：`m = np * t0`，四格后整体下移，`t4' = v + 溢出`。 -/
def red (n0 n1 n2 n3 np k : UInt256) (P : W5) (v : UInt256) : W5 :=
  let m := np * P.t0
  let c0 := redC n0 m P.t0 k
  let c1 := sCarry n1 m c0 P.t1 k
  let c2 := sCarry n2 m c1 P.t2 k
  let c3 := sCarry n3 m c2 P.t3 k
  { t0 := mSum n1 m c0 P.t1, t1 := mSum n2 m c1 P.t2, t2 := mSum n3 m c2 P.t3,
    t3 := P.t4 + c3, t4 := v + UInt256.lt (P.t4 + c3) P.t4 }

/-- 四行之后的五个累加字。 -/
def final (a0 a1 a2 a3 n0 n1 n2 n3 np k : UInt256) : W5 :=
  let W1 := red n0 n1 n2 n3 np k (row0 a0 a1 a2 a3 k) ⟨0⟩
  let R1 := row1 a0 a1 a2 a3 k W1
  let W2 := red n0 n1 n2 n3 np k R1.1 R1.2
  let R2 := row2 a1 a2 a3 k W2
  let W3 := red n0 n1 n2 n3 np k R2.1 R2.2
  let R3 := row3 a2 a3 k W3
  red n0 n1 n2 n3 np k R3.1 R3.2

/-! ## 字级算术引理

`k` 在字节码里是栈上的全 1 字；下列引理都在 `k = maxWord` 下陈述，用处先 `subst`。 -/

open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem toNat_lt (a : UInt256) : a.toNat < 2 ^ 256 := a.val.isLt

theorem toNat_mul (a b : UInt256) : (a * b).toNat = a.toNat * b.toNat % 2 ^ 256 :=
  word_toNat_mul a b

theorem toNat_ltw (a b : UInt256) :
    (UInt256.lt a b).toNat = if a.toNat < b.toNat then 1 else 0 := word_toNat_lt a b

theorem gt_eq_lt (a b : UInt256) : UInt256.gt a b = UInt256.lt b a := rfl

theorem toNat_gtw (a b : UInt256) :
    (UInt256.gt a b).toNat = if b.toNat < a.toNat then 1 else 0 := by
  rw [gt_eq_lt]; exact word_toNat_lt b a

theorem toNat_zero : ((⟨0⟩ : UInt256)).toNat = 0 := rfl

theorem zero_add_w (a : UInt256) : (⟨0⟩ : UInt256) + a = a := by
  apply word_ext
  rw [word_toNat_add, toNat_zero, Nat.zero_add]
  exact Nat.mod_eq_of_lt (toNat_lt a)

theorem lt_zero_w (a : UInt256) : UInt256.lt a ⟨0⟩ = ⟨0⟩ := by
  apply word_ext
  rw [toNat_ltw, toNat_zero, if_neg (Nat.not_lt_zero _)]

/-! ### 与 `Monpro` 的 MAC 步对齐 -/

/-- 零累加格就是 `t = 0` 的 MAC 步（低字）。 -/
theorem zSum_eq (o d c : UInt256) : zSum o d c = macSum o d ⟨0⟩ c := by
  unfold zSum macSum
  rw [zero_add_w]

/-- 零累加格就是 `t = 0` 的 MAC 步（进位）。 -/
theorem zCarry_eq (o d c : UInt256) : zCarry o d c maxWord = macCarry o d ⟨0⟩ c := by
  unfold zCarry macCarry mulHi
  rw [MacAlt.mulMod_comm o d]
  simp only [gt_eq_lt]
  rw [MacAlt.subSubFold, zero_add_w, lt_zero_w, zero_add_w]

/-- 行 0 对角格的高字就是 `mulHi a a`。 -/
theorem dHi_eq (a : UInt256) : dHi a maxWord = mulHi a a := by
  unfold dHi mulHi
  simp only [gt_eq_lt]
  apply word_ext
  have hm := toNat_lt (UInt256.mulMod a a maxWord)
  have hl := toNat_lt (a * a)
  have hb := toNat_lt (UInt256.lt (UInt256.mulMod a a maxWord) (a * a))
  simp only [word_toNat_sub, word_toNat_add, toNat_zero]
  generalize (UInt256.mulMod a a maxWord).toNat = M at *
  generalize (a * a).toNat = L at *
  generalize (UInt256.lt (UInt256.mulMod a a maxWord) (a * a)).toNat = B at *
  omega

/-- **零累加格精确**：`zCarry * R + zSum = o * d + c`。 -/
theorem zCell_spec (o d c : UInt256) :
    (zCarry o d c maxWord).toNat * 2 ^ 256 + (zSum o d c).toNat = o.toNat * d.toNat + c.toNat := by
  have h := macSpec o d ⟨0⟩ c
  have h0 := toNat_zero
  rw [zCarry_eq, zSum_eq]
  omega

/-- 行 0 对角格高字：`dHi * R + a * a = a²`。 -/
theorem dHi_spec (a : UInt256) :
    (dHi a maxWord).toNat * 2 ^ 256 + (a * a).toNat = a.toNat * a.toNat := by
  rw [dHi_eq]; exact mulHi_spec a a

/-! ### 带累加 limb 的格：通用 `K` 上的核心 -/

private theorem prod_le {K x y : Nat} (hx : x < K) (hy : y < K) : x * y ≤ (K - 1) * (K - 1) :=
  Nat.mul_le_mul (by omega) (by omega)

private theorem sq_facts {K : Nat} (hK : 0 < K) :
    (K - 1) * (K - 1) + (K - 1) = (K - 1) * K ∧ (K - 1) * K + K = K * K := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  constructor <;> ring

/-- `Z * K + S = X + c` 且 `X ≤ (K-1)²` 时，再加一个累加 limb `t`：进位字 `Z + [溢出]` 不回绕，
整体仍精确。溢出判据 `P` 可以是 `LT(s, t)` 或 `GT(S, s)`，只要它等价于 `K ≤ S + t`。 -/
private theorem cell_core {K Z S X c t : Nat} (P : Prop) [Decidable P] (hK : 0 < K)
    (hx : X ≤ (K - 1) * (K - 1)) (hc : c < K) (ht : t < K) (hS : S < K)
    (hz : Z * K + S = X + c) (hP : P ↔ K ≤ S + t) :
    ((Z + (if P then 1 else 0)) % K) * K + (S + t) % K = X + c + t := by
  obtain ⟨hA, hB⟩ := sq_facts hK
  rcases Nat.lt_or_ge (S + t) K with h | h
  · rw [Nat.mod_eq_of_lt h, if_neg (fun hp => absurd (hP.mp hp) (by omega)), Nat.add_zero]
    have hZ : Z < K := by
      by_contra hn
      have := Nat.mul_le_mul_right K (Nat.le_of_not_lt hn)
      omega
    rw [Nat.mod_eq_of_lt hZ]
    omega
  · have hv : (S + t) % K = S + t - K := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hv, if_pos (hP.mpr h)]
    have hZ : Z + 1 < K := by
      by_contra hn
      have := Nat.mul_le_mul_right K (show K - 1 ≤ Z by omega)
      omega
    rw [Nat.mod_eq_of_lt hZ, Nat.add_mul, Nat.one_mul]
    omega

/-- **一般格精确（积行）**：`mCarry * R + mSum = o * d + c + t`。 -/
theorem mCell_spec (o d c t : UInt256) :
    (mCarry o d c t maxWord).toNat * 2 ^ 256 + (mSum o d c t).toNat =
      o.toNat * d.toNat + c.toNat + t.toNat := by
  have hz := zCell_spec o d c
  have hS := toNat_lt (zSum o d c)
  have ht := toNat_lt t
  unfold mCarry
  rw [show mSum o d c t = zSum o d c + t from rfl, word_toNat_add, word_toNat_add, toNat_ltw,
    word_toNat_add]
  exact cell_core _ (by norm_num) (prod_le (toNat_lt o) (toNat_lt d)) (toNat_lt c) ht hS hz
    (by
      constructor
      · intro hp; by_contra hn
        rw [Nat.mod_eq_of_lt (by omega)] at hp; omega
      · intro hp
        rw [Nat.mod_eq_sub_mod hp, Nat.mod_eq_of_lt (by omega)]; omega)

/-- **一般格精确（约化行）**：`sCarry * R + mSum = o * d + c + t`。 -/
theorem sCell_spec (o d c t : UInt256) :
    (sCarry o d c t maxWord).toNat * 2 ^ 256 + (mSum o d c t).toNat =
      o.toNat * d.toNat + c.toNat + t.toNat := by
  have hz := zCell_spec o d c
  have hS := toNat_lt (zSum o d c)
  have ht := toNat_lt t
  unfold sCarry
  rw [show mSum o d c t = zSum o d c + t from rfl, word_toNat_add, word_toNat_add, toNat_gtw,
    word_toNat_add]
  exact cell_core _ (by norm_num) (prod_le (toNat_lt o) (toNat_lt d)) (toNat_lt c) ht hS hz
    (by
      constructor
      · intro hp; by_contra hn
        rw [Nat.mod_eq_of_lt (by omega)] at hp; omega
      · intro hp
        rw [Nat.mod_eq_sub_mod hp, Nat.mod_eq_of_lt (by omega)]; omega)

/-! ### 约化首格 -/

/-- `R ≡ 1 (mod R - 1)`：`X mod (R-1) = (X / R + X mod R) mod (R-1)`。 -/
private theorem mod_pred (X : Nat) :
    X % (2 ^ 256 - 1) = (X / 2 ^ 256 + X % 2 ^ 256) % (2 ^ 256 - 1) := by
  have hmodeq : (2 : Nat) ^ 256 ≡ 1 [MOD 2 ^ 256 - 1] := by
    unfold Nat.ModEq; norm_num
  have hstep := (hmodeq.mul_right (X / 2 ^ 256)).add_right (X % 2 ^ 256)
  rw [Nat.one_mul, Nat.div_add_mod] at hstep
  exact hstep

private theorem high_lt' {K X Y : Nat} (hK : 2 ≤ K) (hX : X < K) (hY : Y < K) :
    X * Y / K + 1 < K := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 2 := ⟨K - 2, by omega⟩
  have h1 : X * Y ≤ (K' + 1) * (K' + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : X * Y / (K' + 2) < K' + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; nlinarith
  omega

/-- `m = np * t0` 下 `t0 + n0 * m ≡ 0 (mod R)`（`n0 * np ≡ -1`）。 -/
private theorem mont_zero (n0 np t0 : UInt256)
    (hinv : (n0.toNat * np.toNat + 1) % 2 ^ 256 = 0) :
    (n0.toNat * (np * t0).toNat + t0.toNat) % 2 ^ 256 = 0 := by
  rw [toNat_mul]
  have e : n0.toNat * (np.toNat * t0.toNat % 2 ^ 256) + t0.toNat ≡
      (n0.toNat * np.toNat + 1) * t0.toNat [MOD 2 ^ 256] := by
    have h1 := ((Nat.mod_modEq (np.toNat * t0.toNat) (2 ^ 256)).mul_left n0.toNat).add_right t0.toNat
    calc n0.toNat * (np.toNat * t0.toNat % 2 ^ 256) + t0.toNat
        ≡ n0.toNat * (np.toNat * t0.toNat) + t0.toNat [MOD 2 ^ 256] := h1
      _ = (n0.toNat * np.toNat + 1) * t0.toNat := by ring
  unfold Nat.ModEq at e
  rw [e, Nat.mul_mod, hinv, Nat.zero_mul, Nat.zero_mod]

private theorem redc_core {K H L M X t : Nat} (hK : 2 ≤ K) (hH : H + 1 < K) (hL : L < K)
    (ht : t < K) (hX : X = K * H + L) (hM : M = (H + L) % (K - 1)) (hz : (L + t) % K = 0) :
    (((if (t + M) % K < t then 1 else 0) + (t + M) % K) % K) * K = t + X := by
  have hLt : L + t = 0 ∨ L + t = K := by
    rcases Nat.lt_or_ge (L + t) K with h | h
    · left; rw [Nat.mod_eq_of_lt h] at hz; exact hz
    · right; rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at hz; omega
  have hMv : (H + L < K - 1 ∧ M = H + L) ∨ (K - 1 ≤ H + L ∧ M = H + L - (K - 1)) := by
    rcases Nat.lt_or_ge (H + L) (K - 1) with h | h
    · exact Or.inl ⟨h, by rw [hM, Nat.mod_eq_of_lt h]⟩
    · exact Or.inr ⟨h, by rw [hM, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]⟩
  have hy : (t + M < K ∧ (t + M) % K = t + M) ∨ (K ≤ t + M ∧ (t + M) % K = t + M - K) := by
    rcases Nat.lt_or_ge (t + M) K with h | h
    · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
    · exact Or.inr ⟨h, by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]⟩
  generalize (t + M) % K = y at *
  have hw : ∀ g : Nat, g ≤ 1 → y < K →
      (g + y < K ∧ (g + y) % K = g + y) ∨ (K ≤ g + y ∧ (g + y) % K = g + y - K) := by
    intro g hg hyK
    rcases Nat.lt_or_ge (g + y) K with h | h
    · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
    · exact Or.inr ⟨h, by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]⟩
  have hyK : y < K := by omega
  have hres : ((if y < t then 1 else 0) + y) % K = H ∧ L + t = 0 ∨
      ((if y < t then 1 else 0) + y) % K = H + 1 ∧ L + t = K := by
    split_ifs with hg
    · rcases hw 1 le_rfl hyK with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> omega
    · rcases hw 0 (Nat.zero_le _) hyK with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> omega
  rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, hX, show t = 0 by omega, show L = 0 by omega, Nat.mul_comm]; ring
  · rw [h1, hX, Nat.add_mul, Nat.one_mul, Nat.mul_comm H K]; omega

/-- **约化首格精确**：`redC * R = t0 + n0 * m`（`m = np * t0`，`n0 * np ≡ -1`）。 -/
theorem redC_spec (n0 np t0 : UInt256)
    (hinv : (n0.toNat * np.toNat + 1) % 2 ^ 256 = 0) :
    (redC n0 (np * t0) t0 maxWord).toNat * 2 ^ 256 = t0.toNat + n0.toNat * (np * t0).toNat := by
  have hz := mont_zero n0 np t0 hinv
  have hH := high_lt' (K := 2 ^ 256) (by norm_num) (toNat_lt n0) (toNat_lt (np * t0))
  unfold redC
  rw [word_toNat_add, toNat_gtw, word_toNat_add, word_toNat_mulMod_max]
  generalize n0.toNat * (np * t0).toNat = X at *
  rw [← Nat.mod_add_mod] at hz
  exact redc_core (by norm_num) hH (Nat.mod_lt _ (by norm_num)) (toNat_lt t0)
    (Nat.div_add_mod X _).symm (mod_pred X) hz

local macro "rnum" : tactic =>
  `(tactic| simp only [show (2 : Nat) ^ 256 =
    115792089237316195423570985008687907853269984665640564039457584007913129639936 from by norm_num]
    at *)

/-- `t4` 吸收进位：`[p + c 溢出] * R + (p + c) = p + c`。 -/
theorem add_spec (p c : UInt256) :
    (UInt256.lt (p + c) p).toNat * 2 ^ 256 + (p + c).toNat = p.toNat + c.toNat := by
  have hp := toNat_lt p
  have hc := toNat_lt c
  simp only [word_toNat_add, toNat_ltw]
  rnum
  split_ifs <;> omega

/-- 溢出位 `LT(p + c, p)` 与 `LT(p + c, c)` 相同。 -/
theorem lt_add_left_eq (p c : UInt256) : UInt256.lt (p + c) p = UInt256.lt (p + c) c := by
  apply word_ext
  have hp := toNat_lt p
  have hc := toNat_lt c
  simp only [word_toNat_add, toNat_ltw]
  rnum
  split_ifs <;> omega

/-- 高低字对的唯一性。 -/
theorem pair_unique {a b a' b' : UInt256}
    (h : a.toNat * 2 ^ 256 + b.toNat = a'.toNat * 2 ^ 256 + b'.toNat) : a = a' ∧ b = b' := by
  have hb := toNat_lt b
  have hb' := toNat_lt b'
  have ha := toNat_lt a
  have ha' := toNat_lt a'
  constructor <;> apply word_ext <;> rnum <;> omega

end Challenge.Modexp.Submission.Proofs.Fast.R4Math
