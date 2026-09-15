import Challenge.Modexp.Submission.Proofs.Bytecode.BigCMem

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC.Unsigned

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode.BigC

/-- The exact unsigned expression computed by the 69-byte ADDM cell. -/
def sumWord (mem : ByteArray) (src z i : Nat) (c : UInt256) : UInt256 :=
  c + ((UInt256.ofNat 255 - byteW mem (z + i)) +
    (byteW mem i + byteW mem (src + i)))

def nextCarry (w : UInt256) : UInt256 := UInt256.shiftRight w (UInt256.ofNat 8)

def writeByte (mem : ByteArray) (i : Nat) (w : UInt256) : ByteArray :=
  MachineState.writeBytes mem (ByteArray.mk #[UInt8.ofNat (w.toNat % 256)]) i

theorem small_word {n : Nat} (h : n < 65536) : n < 2 ^ 256 :=
  lt_of_lt_of_le h (by norm_num)

theorem nextCarry_toNat (w : UInt256) : (nextCarry w).toNat = w.toNat / 256 := by
  unfold nextCarry
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by norm_num : 8 < 256),
    Nat.shiftRight_eq_div_pow]

theorem sumWord_toNat (mem : ByteArray) (src z i : Nat) (c : UInt256)
    (hc : c.toNat ≤ 2) :
    (sumWord mem src z i c).toNat =
      c.toNat + ((255 - bget mem (z + i)) + (bget mem i + bget mem (src + i))) := by
  have hx := bget_lt mem i
  have hy := bget_lt mem (src + i)
  have hz := bget_lt mem (z + i)
  have hs : (UInt256.ofNat 255 - byteW mem (z + i)).toNat =
      255 - bget mem (z + i) := by
    rw [Challenge.EvmProof.Word.word_toNat_sub_cond, byteW_toNat]
    norm_num
    omega
  unfold sumWord
  rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_add, hs, byteW_toNat, byteW_toNat,
    Nat.mod_eq_of_lt (small_word (by omega : bget mem i + bget mem (src + i) < 65536)),
    Nat.mod_eq_of_lt (small_word (by omega :
      (255 - bget mem (z + i)) + (bget mem i + bget mem (src + i)) < 65536)),
    Nat.mod_eq_of_lt (small_word (by omega :
      c.toNat + ((255 - bget mem (z + i)) + (bget mem i + bget mem (src + i))) < 65536))]

theorem cell_arithmetic (mem : ByteArray) (src z i : Nat) (c : UInt256)
    (hc : c.toNat ≤ 2) :
    let w := sumWord mem src z i c
    (nextCarry w).toNat ≤ 2 ∧
      w.toNat % 256 + bget mem (z + i) + 256 * (nextCarry w).toNat =
        bget mem i + bget mem (src + i) + 255 + c.toNat := by
  dsimp only
  have hx := bget_lt mem i
  have hy := bget_lt mem (src + i)
  have hz := bget_lt mem (z + i)
  rw [nextCarry_toNat, sumWord_toNat _ _ _ _ _ hc]
  omega

/-- Descending byte pass. Only the first `n` accumulator bytes are written. -/
def pass (src z : Nat) : Nat → ByteArray → UInt256 → ByteArray × UInt256
  | 0, mem, c => (mem, c)
  | n + 1, mem, c =>
    let w := sumWord mem src z n c
    pass src z n (writeByte mem n w) (nextCarry w)

theorem pass_spec (src z : Nat) : ∀ n (mem : ByteArray) (c : UInt256),
    c.toNat ≤ 2 → (src = 0 ∨ n ≤ src) → n ≤ z →
    let result := pass src z n mem c
    result.2.toNat ≤ 2 ∧
      num result.1 0 n + num mem z n + result.2.toNat * 256 ^ n =
        num mem 0 n + num mem src n + (256 ^ n - 1) + c.toNat ∧
      (∀ k, n ≤ k → bget result.1 k = bget mem k) := by
  intro n
  induction n with
  | zero =>
    intro mem c hc _ _
    simp only [pass, num_zero, pow_zero, Nat.sub_self, Nat.mul_one, Nat.zero_add,
      Nat.add_zero]
    exact ⟨hc, trivial, fun _ _ => trivial⟩
  | succ n ih =>
    intro mem c hc hsrc hz
    let w := sumWord mem src z n c
    let m1 := writeByte mem n w
    have hw := cell_arithmetic mem src z n c hc
    change (nextCarry w).toNat ≤ 2 ∧
      w.toNat % 256 + bget mem (z + n) + 256 * (nextCarry w).toNat =
        bget mem n + bget mem (src + n) + 255 + c.toNat at hw
    have hi := ih m1 (nextCarry w) hw.1 (by omega) (by omega)
    dsimp only at hi ⊢
    change (pass src z n m1 (nextCarry w)).2.toNat ≤ 2 ∧
      num (pass src z n m1 (nextCarry w)).1 0 (n + 1) + num mem z (n + 1) +
        (pass src z n m1 (nextCarry w)).2.toNat * 256 ^ (n + 1) =
          num mem 0 (n + 1) + num mem src (n + 1) + (256 ^ (n + 1) - 1) + c.toNat ∧
      (∀ k, n + 1 ≤ k → bget (pass src z n m1 (nextCarry w)).1 k = bget mem k)
    have h0 : num m1 0 n = num mem 0 n := num_congr n (fun j hj => by
      simp only [m1, writeByte, bget_write1, Nat.zero_add]
      rw [if_neg (by omega)])
    have hs : num m1 src n = num mem src n := num_congr n (fun j hj => by
      simp only [m1, writeByte, bget_write1]
      rw [if_neg (by omega)])
    have hZ : num m1 z n = num mem z n := num_congr n (fun j hj => by
      simp only [m1, writeByte, bget_write1]
      rw [if_neg (by omega)])
    have hlast : bget (pass src z n m1 (nextCarry w)).1 n = w.toNat % 256 := by
      rw [hi.2.2 n (le_refl _)]
      simp [m1, writeByte, bget_write1]
    refine ⟨hi.1, ?_, ?_⟩
    · have heq := hi.2.1
      rw [h0, hs, hZ] at heq
      rw [num_succ, num_succ, num_succ, num_succ, Nat.zero_add, hlast, pow_succ]
      have hp : 0 < (256 : Nat) ^ n := pow_pos (by decide) n
      have hmul := congrArg (fun t : Nat => t * 256) heq
      simp only [Nat.add_mul, Nat.mul_assoc] at hmul
      omega
    · intro k hk
      rw [hi.2.2 k (by omega)]
      simp only [m1, writeByte, bget_write1]
      rw [if_neg (by omega)]

/-- Initial carry one expresses addition and subtraction without signed words. -/
theorem pass_one (src z n : Nat) (mem : ByteArray)
    (hs : src = 0 ∨ n ≤ src) (hz : n ≤ z) :
    let result := pass src z n mem (UInt256.ofNat 1)
    result.2.toNat ≤ 2 ∧
      num result.1 0 n + num mem z n + result.2.toNat * 256 ^ n =
        num mem 0 n + num mem src n + 256 ^ n ∧
      (∀ k, n ≤ k → bget result.1 k = bget mem k) := by
  have h := pass_spec src z n mem (UInt256.ofNat 1) (by simp) hs hz
  have hp : 0 < (256 : Nat) ^ n := pow_pos (by decide) n
  dsimp only at h ⊢
  refine ⟨h.1, ?_, h.2.2⟩
  have he := h.2.1
  norm_num at he
  omega

def addResult (ml src : Nat) (mem : ByteArray) : ByteArray :=
  let first := pass src 1024 ml mem (UInt256.ofNat 1)
  if first.2.toNat = 0 then
    (pass 1024 8192 ml first.1 (UInt256.ofNat 1)).1
  else first.1

/-- Exact result/frame contract of ADDM, including its at-most-one retry. -/
theorem addResult_correct (ml src : Nat) (mem : ByteArray)
    (hml : ml ≤ 1024) (hs : src = 0 ∨ ml ≤ src)
    (hzero : num mem 8192 ml = 0)
    (hlt : num mem 0 ml + num mem src ml < 2 * num mem 1024 ml) :
    num (addResult ml src mem) 0 ml =
        (num mem 0 ml + num mem src ml) % num mem 1024 ml ∧
      (∀ k, ml ≤ k → bget (addResult ml src mem) k = bget mem k) := by
  let first := pass src 1024 ml mem (UInt256.ofNat 1)
  have h1 := pass_one src 1024 ml mem hs hml
  change first.2.toNat ≤ 2 ∧
    num first.1 0 ml + num mem 1024 ml + first.2.toNat * 256 ^ ml =
      num mem 0 ml + num mem src ml + 256 ^ ml ∧
    (∀ k, ml ≤ k → bget first.1 k = bget mem k) at h1
  have hR : 0 < (256 : Nat) ^ ml := pow_pos (by decide) ml
  have hM := num_lt mem 1024 ml
  have hF := num_lt first.1 0 ml
  have hM1 : num first.1 1024 ml = num mem 1024 ml :=
    num_congr ml (fun i _ => h1.2.2 _ (by omega))
  have hZ1 : num first.1 8192 ml = 0 := by
    rw [← hzero]
    exact num_congr ml (fun i _ => h1.2.2 _ (by omega))
  by_cases hc0 : first.2.toNat = 0
  · have he1 := h1.2.1
    rw [hc0, Nat.zero_mul, Nat.add_zero] at he1
    have hbelow : num mem 0 ml + num mem src ml < num mem 1024 ml := by omega
    have h2 := pass_one 1024 8192 ml first.1 (Or.inr hml) (by omega)
    let second := pass 1024 8192 ml first.1 (UInt256.ofNat 1)
    change second.2.toNat ≤ 2 ∧
      num second.1 0 ml + num first.1 8192 ml + second.2.toNat * 256 ^ ml =
        num first.1 0 ml + num first.1 1024 ml + 256 ^ ml ∧
      (∀ k, ml ≤ k → bget second.1 k = bget first.1 k) at h2
    have he2 := h2.2.1
    rw [hZ1, Nat.add_zero, hM1, he1] at he2
    have hS := num_lt second.1 0 ml
    have hc2 : second.2.toNat = 0 ∨ second.2.toNat = 1 ∨ second.2.toNat = 2 := by omega
    have hc : second.2.toNat = 2 := by
      rcases hc2 with hc | hc | hc
      · rw [hc, Nat.zero_mul, Nat.add_zero] at he2
        omega
      · rw [hc, Nat.one_mul] at he2
        omega
      · exact hc
    rw [hc] at he2
    have hv : num second.1 0 ml = num mem 0 ml + num mem src ml := by omega
    change num (if first.2.toNat = 0 then second.1 else first.1) 0 ml = _ ∧ _
    rw [if_pos hc0, hv, Nat.mod_eq_of_lt hbelow]
    refine ⟨rfl, ?_⟩
    intro k hk
    change bget (if first.2.toNat = 0 then second.1 else first.1) k = bget mem k
    rw [if_pos hc0, h2.2.2 k hk, h1.2.2 k hk]
  · have hc1 : first.2.toNat = 1 ∨ first.2.toNat = 2 := by omega
    have he1 := h1.2.1
    have hc : first.2.toNat = 1 := by
      rcases hc1 with hc | hc
      · exact hc
      · rw [hc] at he1
        omega
    rw [hc, Nat.one_mul] at he1
    have hge : num mem 1024 ml ≤ num mem 0 ml + num mem src ml := by omega
    have hv : num first.1 0 ml = num mem 0 ml + num mem src ml - num mem 1024 ml := by omega
    have hmod : (num mem 0 ml + num mem src ml) % num mem 1024 ml =
        num mem 0 ml + num mem src ml - num mem 1024 ml := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    change num (if first.2.toNat = 0 then _ else first.1) 0 ml = _ ∧ _
    rw [if_neg hc0, hv, hmod]
    refine ⟨rfl, ?_⟩
    intro k hk
    change bget (if first.2.toNat = 0 then _ else first.1) k = bget mem k
    rw [if_neg hc0]
    exact h1.2.2 k hk

#print axioms pass_spec
#print axioms pass_one
#print axioms addResult_correct

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.Unsigned
