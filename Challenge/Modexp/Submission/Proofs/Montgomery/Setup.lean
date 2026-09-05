import Challenge.Modexp.Submission.Proofs.Montgomery.Domain

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Modexp.Submission.Proofs.Montgomery.Setup

open Challenge.Modexp.Submission.Proofs.Montgomery.CIOS Challenge.Modexp.Submission.Proofs.Montgomery.Domain

/-- Modular doubles from an initial reduced value. -/
def doubleIter (m v : Nat) : Nat → Nat
  | 0 => v
  | d + 1 => (2 * doubleIter m v d) % m

/-- Squares through the actual normalized CIOS recurrence. -/
def squareIter (m np n v : Nat) : Nat → Nat
  | 0 => v
  | s + 1 => mont m np n (squareIter m np n v s) (squareIter m np n v s)

/-- Factor = 2^k; copy Montgomery one, double, then square. -/
def fixedR2 (m np n k : Nat) : Nat :=
  squareIter m np n (doubleIter m (encode m n 1) (2 ^ k * n)) (8 - k)

private theorem encode_mod (m n x : Nat) :
    encode m n (x % m) = encode m n x := by
  simp [encode, Nat.mul_mod]

theorem doubleIter_encode (m n x d : Nat) (hm : 0 < m) :
    doubleIter m (encode m n x) d = encode m n (x * 2 ^ d) := by
  induction d with
  | zero => simp [doubleIter]
  | succ d ih =>
    rw [doubleIter, ih, ← encode_double m n (x * 2 ^ d) hm, encode_mod]
    have hp : 2 * (x * 2 ^ d) = x * 2 ^ (d + 1) := by
      rw [pow_succ]
      ring
    rw [hp]

theorem squareIter_encode (m np n x s : Nat)
    (hm : 0 < m) (hmR : m < R n) (hcop : Nat.Coprime m (R n))
    (hinv : (m * np + 1) % B = 0) :
    squareIter m np n (encode m n x) s = encode m n (x ^ (2 ^ s)) := by
  induction s with
  | zero => simp [squareIter]
  | succ s ih =>
    rw [squareIter, ih, mont_encode_mul m np n _ _ hm hmR hcop hinv]
    rw [pow_succ 2 s, pow_mul, pow_two]

theorem fixed_factor_exponent (n k : Nat) (hk : k ≤ 3) :
    (2 ^ k * n) * 2 ^ (8 - k) = 256 * n := by
  calc
    (2 ^ k * n) * 2 ^ (8 - k) = (2 ^ k * 2 ^ (8 - k)) * n := by ring
    _ = 2 ^ 8 * n := by rw [← pow_add, show k + (8 - k) = 8 by omega]
    _ = 256 * n := by norm_num

theorem fixedR2_correct (m np n k : Nat)
    (_hn : 1 ≤ n) (hm : 0 < m) (hmR : m < R n)
    (hodd : m % 2 = 1) (hk : k ≤ 3) (hinv : (m * np + 1) % B = 0) :
    fixedR2 m np n k = (R n * R n) % m := by
  have hcop := coprime_R_of_odd m n hm hodd
  unfold fixedR2
  rw [doubleIter_encode m n 1 _ hm, squareIter_encode m np n _ _ hm hmR hcop hinv]
  rw [one_mul, ← pow_mul, fixed_factor_exponent n k hk]
  rw [show (2 : Nat) ^ (256 * n) = R n by simp [R, B, pow_mul]]
  rfl

/-- The scanned input needs only the limb-width bound, not b < m. -/
theorem mont_mixed_product (m np n a b : Nat)
    (hm : 0 < m) (_hmR : m < R n) (hcop : Nat.Coprime m (R n))
    (_ha : a < m) (hb : b < R n) (hinv : (m * np + 1) % B = 0) :
    mont m np n b (encode m n a) = (a * b) % m := by
  have he : encode m n a < m := Nat.mod_lt _ hm
  have hc := normalized_contract_of_le b (encode m n a) m np n hm he.le hb hinv
  have hbound : mont m np n b (encode m n a) < m := hc.1
  have hstep : mont m np n b (encode m n a) * R n ≡ b * encode m n a [MOD m] := by
    simpa [mont, R, Nat.ModEq] using hc.2
  have heq : encode m n a ≡ a * R n [MOD m] := Nat.mod_modEq _ _
  have hright : mont m np n b (encode m n a) * R n ≡ (a * b) * R n [MOD m] := by
    calc
      mont m np n b (encode m n a) * R n ≡ b * encode m n a [MOD m] := hstep
      _ ≡ b * (a * R n) [MOD m] := heq.mul_left b
      _ ≡ (a * b) * R n [MOD m] := by
        rw [show b * (a * R n) = (a * b) * R n by ring]
  have hcancel := Nat.ModEq.cancel_right_of_coprime hcop hright
  change mont m np n b (encode m n a) % m = (a * b) % m at hcancel
  rw [Nat.mod_eq_of_lt hbound] at hcancel
  exact hcancel

end Challenge.Modexp.Submission.Proofs.Montgomery.Setup
