import YulSemantics.Dialect.EVMExec
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.BitVec

set_option warningAsError true

/-!
# Algebra of the Yul-side memory functions

`YulSemantics.EVM.EvmState.memory` is a *function* `Nat → UInt8`, and the
MODEXP program talks to it through `YulSemantics.EVM.loadWord`, `storeWord`,
`storeByte`, `readBytes`, and the calldata readers `wordFrom`/`byteFrom`
(all plain definitions in `YulSemantics.Dialect.EVMExec`).

This module develops the pointwise algebra of those functions:

* a numeric characterization of `loadWord` (`loadWord_eq`, `loadWord_toNat`):
  the big-endian value of the 32 bytes, plus byte-wise access
  (`byteAt_loadWord`) and the little-endian byte decomposition of a word
  (`byteSum_eq`);
* load-after-store facts (`loadWord_storeWord_self`,
  `loadWord_storeWord_disjoint`, `storeByte` analogues), commutation of stores
  on disjoint ranges, and `readBytes` after stores;
* calldata facts, in particular the `byte(0, calldataload p)` idiom
  (`byteAt_wordFrom_first`).

Everything here is pure mathematics about the memory functions; no Asm
machine state is mentioned.
-/

namespace Challenge.Modexp.Submission.Proof.YulMem

open YulSemantics.EVM

/-! ## A big-endian byte accumulator -/

/-- The numeric value of the big-endian sequence of `k` bytes of `m` starting
at address `p`: the byte at `p` is the most significant one.  `loadWord`
computes exactly this value (see `loadWord_eq`). -/
def wordVal (m : Nat → UInt8) (p k : Nat) : Nat :=
  (List.range k).foldl (fun acc i => acc * 256 + (m (p + i)).toNat) 0

theorem wordVal_succ (m : Nat → UInt8) (p k : Nat) :
    wordVal m p (k + 1) = wordVal m p k * 256 + (m (p + k)).toNat := by
  simp only [wordVal, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

private theorem u8_lt (b : UInt8) : b.toNat < 256 := UInt8.toNat_lt_size b

theorem wordVal_lt (m : Nat → UInt8) (p k : Nat) : wordVal m p k < 256 ^ k := by
  induction k with
  | zero => simp [wordVal]
  | succ k ih =>
      rw [wordVal_succ, Nat.pow_succ]
      have := u8_lt (m (p + k))
      omega

theorem wordVal_congr {m m' : Nat → UInt8} {p k : Nat}
    (h : ∀ i, i < k → m (p + i) = m' (p + i)) :
    wordVal m p k = wordVal m' p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [wordVal_succ, wordVal_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
        h k (Nat.lt_succ_self k)]

theorem wordVal_div_step (m : Nat → UInt8) (p k : Nat) :
    wordVal m p (k + 1) / 256 = wordVal m p k := by
  rw [wordVal_succ, Nat.mul_comm (wordVal m p k) 256, Nat.add_comm]
  have hb := u8_lt (m (p + k))
  rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hb, Nat.zero_add]

theorem wordVal_mod_last (m : Nat → UInt8) (p k : Nat) :
    wordVal m p (k + 1) % 256 = (m (p + k)).toNat := by
  rw [wordVal_succ, Nat.mul_comm (wordVal m p k) 256, Nat.add_comm,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (u8_lt (m (p + k)))]

theorem wordVal_div (m : Nat → UInt8) (p k j : Nat) (hj : j ≤ k) :
    wordVal m p k / 256 ^ j = wordVal m p (k - j) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
      have hjk : j ≤ k := Nat.le_of_succ_le hj
      have hsub : k - j = (k - (j + 1)) + 1 := by omega
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ih k hjk, hsub, wordVal_div_step]

theorem wordVal_of_zero (p k : Nat) : wordVal (fun _ => 0) p k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wordVal_succ, ih]; simp

/-! ## A splice lemma for bitwise or -/

/-- Or-ing a multiple of `2 ^ k` with a number below `2 ^ k` is addition. -/
private theorem lor_add_splice (k q b : Nat) (hb : b < 2 ^ k) :
    2 ^ k * q ||| b = 2 ^ k * q + b := by
  induction k generalizing q b with
  | zero =>
      have hb0 : b = 0 := by simpa using hb
      subst hb0
      simp
  | succ k ih =>
      have hbit : 2 ^ (k + 1) * q = Nat.bit false (2 ^ k * q) := by
        rw [Nat.pow_succ, Nat.mul_assoc, Nat.bit_val, Bool.toNat_false]
        ring
      rw [hbit]
      induction b using Nat.binaryRec with
      | zero => simp
      | bit bl b' _ =>
          have hbt : bl.toNat ≤ 1 := by cases bl <;> decide
          have hb' : b' < 2 ^ k := by
            simp only [Nat.bit_val, Nat.pow_succ] at hb
            omega
          rw [Nat.lor_bit, ih q b' hb']
          simp only [Nat.bit_val, Bool.false_or, Bool.toNat_false]
          omega

private theorem lor_add_splice_256 (q b : Nat) (hb : b < 256) :
    256 * q ||| b = 256 * q + b := by
  have h8 : (2 : Nat) ^ 8 = 256 := by norm_num
  have h := lor_add_splice 8 q b (by rw [h8]; exact hb)
  rwa [h8] at h

/-! ## The value of `loadWord` -/

private theorem two_pow_256_eq (k : Nat) : (2 : Nat) ^ (8 * k) = 256 ^ k := by
  rw [Nat.pow_mul]

private theorem le_two_pow_256 : (256 : Nat) ≤ 2 ^ 256 := by
  have h : (2 : Nat) ^ 8 ≤ 2 ^ 8 * 2 ^ 248 :=
    Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow (n := 248))
  rw [← Nat.pow_add, show (8 : Nat) + 248 = 256 from rfl,
    show (2 : Nat) ^ 8 = 256 from by norm_num] at h
  exact h

private theorem pow_256_32 : (2 : Nat) ^ 256 = 256 ^ 32 := by
  have h : (2 : Nat) ^ 256 = 2 ^ (8 * 32) := by norm_num
  rw [h, two_pow_256_eq]

/-- The big-endian fold inside `loadWord`/`wordFrom` computes `wordVal`,
as long as no truncation happens (which the bound guarantees). -/
theorem foldl_wordVal {m : Nat → UInt8} {p k : Nat}
    (hlt : wordVal m p k < 2 ^ 256) :
    (List.range k).foldl
        (fun (acc : U256) i =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 (m (p + i)).toNat) 0 =
      BitVec.ofNat 256 (wordVal m p k) := by
  induction k with
  | zero => simp [wordVal]
  | succ k ih =>
      rw [wordVal_succ] at hlt
      have hbyte := u8_lt (m (p + k))
      have hE : wordVal m p k < 2 ^ 256 := by omega
      have hE256 : wordVal m p k * 256 < 2 ^ 256 :=
        Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt
      have hb256 : (m (p + k)).toNat < 2 ^ 256 :=
        Nat.lt_of_lt_of_le hbyte le_two_pow_256
      rw [List.range_succ, List.foldl_append, ih hE, List.foldl_cons,
        List.foldl_nil, wordVal_succ]
      apply BitVec.toNat_injective
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_or, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq]
      rw [show (2 : Nat) ^ 8 = 256 from by norm_num, Nat.mod_eq_of_lt hE,
        Nat.mod_eq_of_lt hE256, Nat.mod_eq_of_lt hb256, Nat.mod_eq_of_lt hlt,
        Nat.mul_comm (wordVal m p k) 256]
      exact lor_add_splice_256 (wordVal m p k) _ hbyte

theorem loadWord_eq (m : Nat → UInt8) (p : Nat) :
    loadWord m p = BitVec.ofNat 256 (wordVal m p 32) := by
  have hlt := wordVal_lt m p 32
  rw [← pow_256_32] at hlt
  have h := foldl_wordVal (m := m) (p := p) (k := 32) hlt
  unfold loadWord
  exact h

theorem loadWord_toNat (m : Nat → UInt8) (p : Nat) :
    (loadWord m p).toNat = wordVal m p 32 := by
  rw [loadWord_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact wordVal_lt m p 32

theorem loadWord_zero (p : Nat) : loadWord (fun _ => 0) p = 0 := by
  rw [loadWord_eq, wordVal_of_zero]
  rfl

/-! ## Bytes of a word -/

private theorem mod_mul_div (v c q : Nat) (hc : 0 < c) (hq : 0 < q) :
    v % (c * q) / q = v / q % c := by
  have hB : v % q < q := Nat.mod_lt _ hq
  have hX : v / q % c < c := Nat.mod_lt _ hc
  have hcomm : c * q = q * c := Nat.mul_comm c q
  have key : q * (v / q % c) + q ≤ q * c := by
    calc q * (v / q % c) + q = q * (v / q % c + 1) := by ring
      _ ≤ q * c := Nat.mul_le_mul_left q (by omega)
  have hlt : q * (v / q % c) + v % q < c * q := by omega
  have hv : c * q * (v / q / c) + (q * (v / q % c) + v % q) = v := by
    calc c * q * (v / q / c) + (q * (v / q % c) + v % q)
        = q * (c * (v / q / c) + v / q % c) + v % q := by ring
      _ = q * (v / q) + v % q := by rw [Nat.div_add_mod]
      _ = v := Nat.div_add_mod v q
  have h1 : v % (c * q) = (c * q * (v / q / c) + (q * (v / q % c) + v % q)) %
      (c * q) := by rw [hv]
  rw [h1, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
    Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hB, Nat.zero_add]

private theorem byteSum_mod (v n : Nat) :
    (List.range n).foldl (fun acc j => acc + (v / 256 ^ j % 256) * 256 ^ j) 0 =
      v % 256 ^ n := by
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256,
        Nat.mul_comm (v / 256 ^ n % 256) (256 ^ n)]
      have hq : (0 : Nat) < 256 ^ n := by
        rw [← two_pow_256_eq]
        exact Nat.two_pow_pos _
      have h1 := Nat.div_add_mod (v % (256 * 256 ^ n)) (256 ^ n)
      have h2 : v % (256 * 256 ^ n) / 256 ^ n = v / 256 ^ n % 256 :=
        mod_mul_div v 256 (256 ^ n) (by norm_num) hq
      rw [h2] at h1
      have h3 : v % (256 * 256 ^ n) % 256 ^ n = v % 256 ^ n :=
        Nat.mod_mod_of_dvd v (Nat.dvd_mul_left (256 ^ n) 256)
      omega

/-- The little-endian byte decomposition of a 256-bit word. -/
def byteSum (w : U256) : Nat :=
  (List.range 32).foldl (fun acc j => acc + (byteAt w j).toNat * 256 ^ j) 0

theorem byteAt_toNat_div (w : U256) (j : Nat) :
    (byteAt w j).toNat = w.toNat / 256 ^ j % 256 := by
  simp only [byteAt, UInt8.toNat_ofNat', BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [two_pow_256_eq]

theorem byteSum_eq (w : U256) : byteSum w = w.toNat := by
  have hfun : (fun acc j => acc + (byteAt w j).toNat * 256 ^ j) =
      fun acc j => acc + (w.toNat / 256 ^ j % 256) * 256 ^ j := by
    funext acc j
    rw [byteAt_toNat_div]
  have hlt : w.toNat < 256 ^ 32 := by
    rw [← two_pow_256_eq]
    simpa using BitVec.isLt w
  rw [byteSum, hfun, byteSum_mod, Nat.mod_eq_of_lt hlt]

theorem byteAt_loadWord (m : Nat → UInt8) (p j : Nat) (hj : j < 32) :
    byteAt (loadWord m p) j = m (p + (31 - j)) := by
  apply UInt8.toNat_inj.mp
  rw [byteAt_toNat_div, loadWord_toNat, wordVal_div m p 32 j (Nat.le_of_lt hj)]
  have hsub : 32 - j = (31 - j) + 1 := by omega
  rw [hsub, wordVal_mod_last]

/-! ## Load after store -/

@[simp] theorem storeWord_self (m : Nat → UInt8) (p : Nat) (v : U256) (a : Nat)
    (h1 : p ≤ a) (h2 : a < p + 32) :
    storeWord m p v a = byteAt v (31 - (a - p)) := by
  simp [storeWord, h1, h2]

@[simp] theorem storeWord_other (m : Nat → UInt8) (p : Nat) (v : U256) (a : Nat)
    (h : ¬(p ≤ a ∧ a < p + 32)) :
    storeWord m p v a = m a := by
  simp [storeWord, h]

@[simp] theorem storeByte_self (m : Nat → UInt8) (p : Nat) (v : U256) :
    storeByte m p v p = byteAt v 0 := by
  simp [storeByte]

@[simp] theorem storeByte_other (m : Nat → UInt8) (p : Nat) (v : U256) (a : Nat)
    (h : a ≠ p) :
    storeByte m p v a = m a := by
  simp [storeByte, h]

/-- Reading a word only depends on the bytes in its own range. -/
theorem loadWord_congr {m m' : Nat → UInt8} {p : Nat}
    (h : ∀ a, p ≤ a → a < p + 32 → m a = m' a) :
    loadWord m p = loadWord m' p := by
  apply BitVec.toNat_injective
  rw [loadWord_toNat, loadWord_toNat]
  exact wordVal_congr fun i hi => h (p + i) (by omega) (by omega)

private theorem foldl_range_congr {α : Type} {f g : α → Nat → α} {x : α} {n : Nat}
    (h : ∀ j (acc : α), j < n → f acc j = g acc j) :
    List.foldl f x (List.range n) = List.foldl g x (List.range n) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_append,
        ih (fun j acc hj => h j acc (Nat.lt_succ_of_lt hj)), List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact h n _ (Nat.lt_succ_self n)

theorem wordVal_eq_byteSum (m : Nat → UInt8) (p : Nat) :
    wordVal m p 32 =
      (List.range 32).foldl (fun acc j => acc + (m (p + (31 - j))).toNat * 256 ^ j) 0 := by
  have h1 := byteSum_eq (loadWord m p)
  rw [loadWord_toNat] at h1
  unfold byteSum at h1
  have hcongr := foldl_range_congr
    (f := fun acc j => acc + (byteAt (loadWord m p) j).toNat * 256 ^ j)
    (g := fun acc j => acc + (m (p + (31 - j))).toNat * 256 ^ j)
    (x := 0) (n := 32)
    (h := fun j _ hj => by simp [byteAt_loadWord m p j hj])
  rw [hcongr] at h1
  exact h1.symm

/-- Storing a word and reading it back. -/
theorem loadWord_storeWord_self (m : Nat → UInt8) (p : Nat) (v : U256) :
    loadWord (storeWord m p v) p = v := by
  apply BitVec.toNat_injective
  rw [loadWord_toNat, wordVal_eq_byteSum]
  have hcongr := foldl_range_congr
    (f := fun acc j => acc + (storeWord m p v (p + (31 - j))).toNat * 256 ^ j)
    (g := fun acc j => acc + (byteAt v j).toNat * 256 ^ j)
    (x := 0) (n := 32)
    (h := fun j _ hj => by
      simp only [storeWord_self m p v (p + (31 - j)) (by omega) (by omega),
        show 31 - ((p + (31 - j)) - p) = j from by omega])
  rw [hcongr]
  exact byteSum_eq v

/-- Storing outside a word's range does not change the word. -/
theorem loadWord_storeWord_disjoint {m : Nat → UInt8} {p q : Nat} {v : U256}
    (h : p + 32 ≤ q ∨ q + 32 ≤ p) :
    loadWord (storeWord m p v) q = loadWord m q := by
  rw [loadWord_congr]
  intro a ha1 ha2
  exact storeWord_other m p v a (by omega)

/-- Storing a single byte outside a word's range does not change the word. -/
theorem loadWord_storeByte_disjoint {m : Nat → UInt8} {p q : Nat} {v : U256}
    (h : q + 32 ≤ p ∨ p < q) :
    loadWord (storeByte m p v) q = loadWord m q := by
  rw [loadWord_congr]
  intro a ha1 ha2
  exact storeByte_other m p v a (by omega)

/-! ## Commuting stores -/

theorem storeWord_storeWord_self (m : Nat → UInt8) (p : Nat) (v w : U256) :
    storeWord (storeWord m p v) p w = storeWord m p w := by
  funext a
  simp only [storeWord]
  split_ifs <;> rfl

theorem storeWord_comm_disjoint {m : Nat → UInt8} {p q : Nat} {v w : U256}
    (h : p + 32 ≤ q ∨ q + 32 ≤ p) :
    storeWord (storeWord m p v) q w = storeWord (storeWord m q w) p v := by
  funext a
  simp only [storeWord]
  split_ifs
  · omega
  · rfl
  · rfl
  · rfl

theorem storeByte_comm_ne {m : Nat → UInt8} {p q : Nat} {v w : U256}
    (h : p ≠ q) :
    storeByte (storeByte m p v) q w = storeByte (storeByte m q w) p v := by
  funext a
  simp only [storeByte]
  split_ifs
  · omega
  · rfl
  · rfl
  · rfl

theorem storeWord_storeByte_comm_disjoint {m : Nat → UInt8} {p q : Nat}
    {v w : U256} (h : p + 32 ≤ q ∨ q + 32 ≤ p) :
    storeWord (storeByte m q w) p v = storeByte (storeWord m p v) q w := by
  funext a
  simp only [storeWord, storeByte]
  split_ifs
  · omega
  · rfl
  · rfl
  · rfl

/-! ## Reading raw byte ranges -/

/-- A byte-range read only depends on the bytes in its own range. -/
theorem readBytes_congr {m m' : Nat → UInt8} {p n : Nat}
    (h : ∀ a, p ≤ a → a < p + n → m a = m' a) :
    readBytes m p n = readBytes m' p n := by
  simp only [readBytes]
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < n := List.mem_range.mp hi
  exact h (p + i) (by omega) (by omega)

theorem readBytes_storeWord_disjoint {m : Nat → UInt8} {p q n : Nat} {v : U256}
    (h : p + 32 ≤ q ∨ q + n ≤ p) :
    readBytes (storeWord m p v) q n = readBytes m q n := by
  rw [readBytes_congr]
  intro a ha1 ha2
  exact storeWord_other m p v a (by omega)

theorem readBytes_storeByte_disjoint {m : Nat → UInt8} {p q n : Nat} {v : U256}
    (h : p < q ∨ q + n ≤ p) :
    readBytes (storeByte m p v) q n = readBytes m q n := by
  rw [readBytes_congr]
  intro a ha1 ha2
  exact storeByte_other m p v a (by omega)

theorem readBytes_storeWord_self (m : Nat → UInt8) (p : Nat) (v : U256) :
    readBytes (storeWord m p v) p 32 = (List.range 32).map fun i => byteAt v (31 - i) := by
  simp only [readBytes, storeWord]
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < 32 := List.mem_range.mp hi
  rw [if_pos (show p ≤ p + i ∧ p + i < p + 32 by omega),
    show 31 - (p + i - p) = 31 - i from by omega]

/-! ## Calldata -/

/-- `wordFrom` is `loadWord` on the zero-padded calldata byte function. -/
theorem wordFrom_eq (data : List UInt8) (p : Nat) :
    wordFrom data p = loadWord (byteFrom data) p := rfl

theorem wordFrom_toNat (data : List UInt8) (p : Nat) :
    (wordFrom data p).toNat = wordVal (byteFrom data) p 32 := by
  rw [wordFrom_eq, loadWord_toNat]

/-- The `j`-th byte (from the little end) of `calldataload p`. -/
theorem byteAt_wordFrom {data : List UInt8} {p j : Nat} (hj : j < 32) :
    byteAt (wordFrom data p) j = byteFrom data (p + (31 - j)) := by
  rw [wordFrom_eq]
  exact byteAt_loadWord (byteFrom data) p j hj

/-- The `byte(0, calldataload p)` idiom: EVM byte 0 is the most significant
byte, which is the calldata byte at address `p`. -/
theorem byteAt_wordFrom_first (data : List UInt8) (p : Nat) :
    byteAt (wordFrom data p) 31 = byteFrom data p := by
  have h := byteAt_wordFrom (data := data) (p := p) (j := 31) (by omega)
  simpa using h

end Challenge.Modexp.Submission.Proof.YulMem
