import Challenge.EvmProof.Word
import Challenge.EvmProof.Stepper
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Abel

set_option warningAsError true

/-!
Pure MONPRO definitions and reassociation facts extracted from the unchanged
broad-window foundation. Public names, types, and models are preserved;
the wrapping-subtraction proof uses the underlying finite additive group.
This module has no Artifact, concrete PC, or submission-correctness dependency.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Monpro

open EvmSemantics EvmSemantics.EVM
theorem word_toNat_lt' (a b : UInt256) :
    (UInt256.lt a b).toNat = if a.toNat < b.toNat then 1 else 0 :=
  Challenge.EvmProof.Word.word_toNat_lt a b

theorem word_lt_size (a : UInt256) : a.toNat < 2 ^ 256 := a.val.isLt

/-- The `PUSH32` immediate the 512-bit multiply uses as the `MULMOD` modulus. -/
def maxWord : UInt256 :=
  UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935

theorem maxWord_toNat : maxWord.toNat = 2 ^ 256 - 1 := by
  rw [maxWord, Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num

theorem word_toNat_mulMod_max (a b : UInt256) :
    (UInt256.mulMod a b maxWord).toNat = a.toNat * b.toNat % (2 ^ 256 - 1) := by
  have hne : maxWord.val.val ≠ 0 := by
    have : maxWord.toNat = 2 ^ 256 - 1 := maxWord_toNat
    change maxWord.toNat ≠ 0
    omega
  rw [UInt256.mulMod, if_neg hne, Challenge.EvmProof.Word.word_toNat_ofNat,
    maxWord_toNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
    (Nat.mod_lt _ (by norm_num)) (by norm_num))


/-- The high word of the 512-bit product, exactly as the bytecode computes it. -/
def mulHi (x y : UInt256) : UInt256 :=
  UInt256.mulMod x y maxWord - (x * y + UInt256.lt (UInt256.mulMod x y maxWord) (x * y))


/-- The stored limb of one multiply-accumulate step. -/
def macSum (x y t c : UInt256) : UInt256 := c + (t + x * y)

/-- The carry out of one multiply-accumulate step. -/
def macCarry (x y t c : UInt256) : UInt256 :=
  UInt256.lt (c + (t + x * y)) c + (UInt256.lt (t + x * y) t + mulHi x y)


namespace MacAlt

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.EvmProof.Word

theorem mulMod_comm (a b : UInt256) :
    UInt256.mulMod b a maxWord = UInt256.mulMod a b maxWord := by
  apply word_ext
  rw [word_toNat_mulMod_max, word_toNat_mulMod_max, Nat.mul_comm]

theorem macSumNat (x y t c : UInt256) :
    (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = (c.toNat + (t.toNat + (x * y).toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  congr 1
  omega

/-- Wrapping subtraction reassociates: `a - (b - d) - e = a + (d - (e + b))`. -/
theorem subSubFold (a b d e : UInt256) :
    a - (b - d) - e = a + (d - (e + b)) := by
  change UInt256.mk (a.val - (b.val - d.val) - e.val) =
    UInt256.mk (a.val + (d.val - (e.val + b.val)))
  congr 1
  abel

/-- The two carry bits of the reassociated sum add up to the same total. -/
theorem carryPair (x y t c : UInt256) :
    (if (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
       then 1 else 0) +
      (if ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < c.toNat then 1 else 0) =
    (UInt256.lt (c + (t + x * y)) c).toNat + (UInt256.lt (t + x * y) t).toNat := by
  have ha : (x * y).toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size (x * y); norm_num at h; exact h
  have hc : c.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size c; norm_num at h; exact h
  have ht : t.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size t; norm_num at h; exact h
  simp only [word_toNat_lt', word_toNat_add,
    show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by norm_num]
  obtain ⟨q1, r1, hq1, hr1, he1⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ (x * y).toNat + c.toNat = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨((x * y).toNat + c.toNat) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936,
      by omega, by omega, by omega⟩
  obtain ⟨q2, r2, hq2, hr2, he2⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ t.toNat + (x * y).toNat = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨(t.toNat + (x * y).toNat) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, (t.toNat + (x * y).toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936,
      by omega, by omega, by omega⟩
  obtain ⟨q3, r3, hq3, hr3, he3⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ t.toNat + r1 = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨(t.toNat + r1) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, (t.toNat + r1) % 115792089237316195423570985008687907853269984665640564039457584007913129639936, by omega, by omega, by omega⟩
  obtain ⟨q4, r4, hq4, hr4, he4⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ c.toNat + r2 = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨(c.toNat + r2) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, (c.toNat + r2) % 115792089237316195423570985008687907853269984665640564039457584007913129639936, by omega, by omega, by omega⟩
  have m1 : ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r1 := by omega
  have m2 : (t.toNat + (x * y).toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r2 := by omega
  have m3 : (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r3 := by omega
  have m4 : (c.toNat + r2) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r4 := by omega
  rw [m1, m2, m3, m4]
  split_ifs <;> omega


theorem ifBit_toNat (P : Prop) [Decidable P] :
    (if P then (UInt256.ofNat 1) else UInt256.ofNat 0).toNat = if P then 1 else 0 := by
  split <;> simp

theorem bit_le (P : Prop) [Decidable P] : (if P then 1 else 0) ≤ 1 := by
  split <;> simp

/-- The carry the reassociated body computes is `macCarry`. -/
theorem macCarryFix (x y t c : UInt256) :
    (if (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 then
        (UInt256.ofNat 1) else UInt256.ofNat 0) +
      (((if ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < c.toNat then (UInt256.ofNat 1)
            else UInt256.ofNat 0) -
          (UInt256.lt (UInt256.mulMod y x maxWord) (x * y) - UInt256.mulMod y x maxWord)) -
        x * y) =
      UInt256.lt (c + (t + x * y)) c + (UInt256.lt (t + x * y) t + mulHi x y) := by
  rw [mulMod_comm, subSubFold]
  have hp := carryPair x y t c
  have hH : (mulHi x y).toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size (mulHi x y); norm_num at h; exact h
  have hb1 := bit_le ((t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)
  have hb2 := bit_le (((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < c.toNat)
  apply word_ext
  simp only [word_toNat_add, ifBit_toNat, word_toNat_lt', mulHi,
    show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by norm_num] at hp ⊢
  omega

end MacAlt

def ptrAt (base j : Nat) : Nat :=
  base + j * 115792089237316195423570985008687907853269984665640564039457584007913129639904

@[simp] theorem ptrAt_zero (base : Nat) : ptrAt base 0 = base := by
  simp [ptrAt]

theorem ptrAt_succ (base j : Nat) :
    115792089237316195423570985008687907853269984665640564039457584007913129639904 +
        ptrAt base j = ptrAt base (j + 1) := by
  simp only [ptrAt, Nat.succ_mul]
  omega

theorem ptrAt_toNat (base j : Nat) (hj : 32 * j ≤ base) (hbase : base < 2 ^ 256) :
    (UInt256.ofNat (ptrAt base j)).toNat = base - 32 * j := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, ptrAt]
  have hlit : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      Nat) = 2 ^ 256 - 32 := by norm_num
  have hmul : j * 115792089237316195423570985008687907853269984665640564039457584007913129639904
      = j * 2 ^ 256 - 32 * j := by
    rw [hlit, Nat.mul_sub, Nat.mul_comm j 32]
  rw [hmul]
  have hrewrite : base + (j * 2 ^ 256 - 32 * j) = (base - 32 * j) + j * 2 ^ 256 := by
    have hle : 32 * j ≤ j * 2 ^ 256 := by
      have := Nat.mul_le_mul_right j (show 32 ≤ 2 ^ 256 by norm_num)
      omega
    omega
  rw [hrewrite, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

theorem ptrAt_mod (base j : Nat) (hj : 32 * j ≤ base) (hbase : base < 2 ^ 256) :
    ptrAt base j %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      base - 32 * j := by
  have hlit : (115792089237316195423570985008687907853269984665640564039457584007913129639936 :
      Nat) = 2 ^ 256 := by norm_num
  rw [hlit, ← Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ptrAt_toNat base j hj hbase

/-! ## Active words

Every address `MONPRO` touches lies below `0x2500`, so once the setup block has
made `0x2500` bytes active no access here extends the high-water mark. -/

theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9472) (hcurr : 296 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  have hle : (off + sz - 1) / 32 + 1 ≤ curr := by omega
  exact Nat.max_eq_left hle

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9472) (hact : 296 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm


/-- Memory together with a running carry. -/
structure MacState where
  memory : ByteArray
  carry : UInt256


/-- Memory and carry after `j` steps of the first limb loop of a row:
step `j` accumulates `a[j] * b[i]` into `t[j]`. -/
def l1Step (mem : ByteArray) (bi : UInt256) (pa n : Nat) : Nat → MacState
  | 0 => ⟨mem, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := l1Step mem bi pa n j
      let x := MachineState.readWord prev.memory (pa + 32 * (n - 1 - j))
      let t := MachineState.readWord prev.memory (8256 + 32 * (n - 1 - j))
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded (macSum x bi t prev.carry).toNat 32)
          (8256 + 32 * (n - 1 - j))
        carry := macCarry x bi t prev.carry }


/-- Memory and carry after `k` steps of the second limb loop.  Step `k`
accumulates `m[k+1] * mu` into `t[k+1]` and stores the result one limb down. -/
def l2Step (mem : ByteArray) (mu c0 : UInt256) (n : Nat) : Nat → MacState
  | 0 => ⟨mem, c0⟩
  | k + 1 =>
      let prev := l2Step mem mu c0 n k
      let x := MachineState.readWord prev.memory (32 * (n - 2 - k))
      let t := MachineState.readWord prev.memory (8256 + 32 * (n - 2 - k))
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded (macSum x mu t prev.carry).toNat 32)
          (8256 + 32 * (n - 1 - k))
        carry := macCarry x mu t prev.carry }


end Challenge.Modexp.Submission.Proofs.Fast.Monpro
