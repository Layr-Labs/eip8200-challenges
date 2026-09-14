import Challenge.Modexp.Submission.Proofs.Bytecode.BigCRun
import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.EvmProof.Bytes
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
/-!
# Compact multi-limb fallback: memory as numbers

Pointwise byte view of EVM memory and the big-endian value of a byte window,
plus metered reachability composition; no artifact or located path dependency.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-! ## Environment and reachability -/

/-- A metered execution exists from `a` to `b`. -/
abbrev Reach (a b : State) : Prop := Nonempty (Challenge.EvmProof.GasSteps a b)

theorem Reach.tr {a b c : State} (h1 : Reach a b) (h2 : Reach b c) : Reach a c := by
  obtain ⟨x⟩ := h1
  obtain ⟨y⟩ := h2
  exact ⟨x.trans y⟩

theorem Reach.rfl' (a : State) : Reach a a := ⟨Challenge.EvmProof.GasSteps.refl a⟩

/-! ## Bytes -/

/-- Memory byte `k` (zero past the end). -/
def bget (mem : ByteArray) (k : Nat) : Nat := (mem[k]?.getD 0).toNat

/-- Big-endian value of the `n` bytes at `a`. -/
abbrev num (mem : ByteArray) (a n : Nat) : Nat := Precompile.bytesToNatPadded mem a n

theorem bget_lt (mem : ByteArray) (k : Nat) : bget mem k < 256 :=
  (mem[k]?.getD 0).toNat_lt

theorem byteFrom_eq (mem : ByteArray) (k : Nat) :
    YulSemantics.EVM.byteFrom mem.toList k = mem[k]?.getD 0 := by
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rfl

theorem num_zero (mem : ByteArray) (a : Nat) : num mem a 0 = 0 :=
  Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width mem a

theorem num_succ (mem : ByteArray) (a n : Nat) :
    num mem a (n + 1) = num mem a n * 256 + bget mem (a + n) := by
  unfold num
  rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ, byteFrom_eq]
  rfl

theorem num_lt (mem : ByteArray) (a n : Nat) : num mem a n < 256 ^ n :=
  Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow mem a n

theorem num_congr {m1 m2 : ByteArray} {a : Nat} :
    ∀ n, (∀ i, i < n → bget m1 (a + i) = bget m2 (a + i)) → num m1 a n = num m2 a n
  | 0, _ => by rw [num_zero, num_zero]
  | n + 1, h => by
    rw [num_succ, num_succ, num_congr n (fun i hi => h i (by omega)), h n (by omega)]

theorem num_eq_zero {mem : ByteArray} {a : Nat} :
    ∀ n, (∀ i, i < n → bget mem (a + i) = 0) → num mem a n = 0
  | 0, _ => num_zero mem a
  | n + 1, h => by
    rw [num_succ, num_eq_zero n (fun i hi => h i (by omega)), h n (by omega)]

theorem bget_write (mem data : ByteArray) (off k : Nat) :
    bget (MachineState.writeBytes mem data off) k =
      if off ≤ k ∧ k < off + data.size then bget data (k - off) else bget mem k := by
  unfold bget
  rw [MachineState.writeBytes_getElem?_getD]
  split <;> rfl

theorem bget_readPadded (bs : ByteArray) (start n i : Nat) :
    bget (MachineState.readPadded bs start n) i =
      if i < n then bget bs (start + i) else 0 := by
  unfold bget
  rw [Challenge.EvmProof.Memory.readPadded_getElem?_getD]
  split <;> rfl

theorem bget_of_size_le (bs : ByteArray) (k : Nat) (h : bs.size ≤ k) : bget bs k = 0 := by
  unfold bget
  rw [Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le bs k h]
  rfl

theorem bget_copy (mem src : ByteArray) (off n dst k : Nat) :
    bget (MachineState.writeBytes mem (MachineState.readPadded src off n) dst) k =
      if dst ≤ k ∧ k < dst + n then bget src (off + (k - dst)) else bget mem k := by
  rw [bget_write, Challenge.EvmProof.Memory.readPadded_size]
  by_cases h : dst ≤ k ∧ k < dst + n
  · rw [if_pos h, if_pos h, bget_readPadded, if_pos (by omega)]
  · rw [if_neg h, if_neg h]

theorem bget_write1 (mem : ByteArray) (v off k : Nat) :
    bget (MachineState.writeBytes mem (ByteArray.mk #[UInt8.ofNat v]) off) k =
      if k = off then v % 256 else bget mem k := by
  rw [bget_write]
  have hs : (ByteArray.mk #[UInt8.ofNat v]).size = 1 := rfl
  rw [hs]
  by_cases h : k = off
  · subst h
    rw [if_pos ⟨le_refl _, by omega⟩, if_pos rfl, Nat.sub_self]
    show (UInt8.ofNat v).toNat = v % 256
    simp [UInt8.toNat_ofNat]
  · rw [if_neg (by omega), if_neg h]

/-- A calldata copy from the end of calldata writes zeros. -/
theorem bget_zeroCopy (mem cd : ByteArray) (n dst k : Nat) :
    bget (MachineState.writeBytes mem (MachineState.readPadded cd cd.size n) dst) k =
      if dst ≤ k ∧ k < dst + n then 0 else bget mem k := by
  rw [bget_copy]
  by_cases h : dst ≤ k ∧ k < dst + n
  · rw [if_pos h, if_pos h]
    exact bget_of_size_le _ _ (by omega)
  · rw [if_neg h, if_neg h]

theorem byteW_toNat (mem : ByteArray) (k : Nat) : (byteW mem k).toNat = bget mem k := by
  unfold byteW
  rw [← zero_lit, Challenge.EvmProof.Bytes.byteAt_zero_readWord,
    Challenge.EvmProof.Word.word_toNat_ofNat, byteFrom_eq]
  exact Nat.mod_eq_of_lt (lt_trans (bget_lt mem k) (by norm_num))

theorem num_one (mem : ByteArray) (a : Nat) : num mem a 1 = bget mem a := by
  have h := num_succ mem a 0
  rw [num_zero] at h
  simpa using h

theorem bitWord_toNat (mem : ByteArray) (a r : Nat) (hr : r < 8) :
    (bitWord mem a r).toNat = bget mem a / 2 ^ (7 - r) % 2 := by
  unfold bitWord
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by norm_num : 255 < 256)]
  have hl : (UInt256.shiftLeft (MachineState.readWord mem a) (UInt256.ofNat r)).toNat =
      (MachineState.readWord mem a).toNat * 2 ^ r % 2 ^ 256 := by
    unfold UInt256.shiftLeft
    have hr' : (UInt256.ofNat r).toNat = r := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hr', if_neg (by omega), Challenge.EvmProof.Word.word_toNat_ofNat, Nat.shiftLeft_eq,
      show UInt256.size = 2 ^ 256 from rfl, Nat.mod_mod]
  rw [hl, Nat.shiftRight_eq_div_pow]
  have h256 : (2 : Nat) ^ 256 = 2 ^ 255 * 2 := by norm_num
  rw [h256, Nat.mod_mul_right_div_self]
  have hW : (MachineState.readWord mem a).toNat / 2 ^ 248 = bget mem a := by
    have h := Challenge.EvmProof.Bytes.readWord_shift_toNat mem a 1 (by norm_num)
    rw [Nat.shiftRight_eq_div_pow, show (32 - 1) * 8 = 248 by norm_num] at h
    rw [h]
    exact num_one mem a
  have hsplit : (2 : Nat) ^ 255 = 2 ^ r * 2 ^ (255 - r) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, Nat.mul_comm (MachineState.readWord mem a).toNat,
    Nat.mul_div_mul_left _ _ (by positivity)]
  have hsplit2 : (2 : Nat) ^ (255 - r) = 2 ^ 248 * 2 ^ (7 - r) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit2, ← Nat.div_div_eq_div_mul, hW]

/-- Byte `k` of a window is the corresponding base-256 digit of its value. -/
theorem bget_of_num (mem : ByteArray) (a : Nat) :
    ∀ n k, k < n → bget mem (a + k) = num mem a n / 256 ^ (n - 1 - k) % 256
  | 0, k, h => absurd h (by omega)
  | n + 1, k, h => by
    rw [num_succ]
    have hb := bget_lt mem (a + n)
    by_cases hk : k = n
    · subst hk
      rw [show k + 1 - 1 - k = 0 by omega, pow_zero, Nat.div_one]
      omega
    · have hk' : k < n := by omega
      rw [show n + 1 - 1 - k = (n - 1 - k) + 1 by omega, pow_succ',
        ← Nat.div_div_eq_div_mul]
      have hdiv : (num mem a n * 256 + bget mem (a + n)) / 256 = num mem a n := by omega
      rw [hdiv]
      exact bget_of_num mem a n k hk'

theorem readPadded_eq_natToBytes (mem : ByteArray) (a n : Nat) :
    MachineState.readPadded mem a n = Precompile.natToBytes (num mem a n) n := by
  apply ByteArray.ext_getElem
  · simp [Precompile.natToBytes, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro k h1 h2
    have hk : k < n := by simpa using h1
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h1,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h2,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hk, Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hk]
    apply UInt8.toNat_inj.mp
    have h := bget_of_num mem a n k hk
    unfold bget at h
    rw [h]
    simp

theorem num_copy (mem src : ByteArray) (off n dst : Nat) :
    num (MachineState.writeBytes mem (MachineState.readPadded src off n) dst) dst n =
      num src off n := by
  have h := Challenge.EvmProof.Memory.readPadded_writeBytes_same mem
    (MachineState.readPadded src off n) dst
  rw [Challenge.EvmProof.Memory.readPadded_size] at h
  unfold num Precompile.bytesToNatPadded
  rw [h]

theorem readWord_congr {m1 m2 : ByteArray} {a : Nat}
    (h : ∀ i, i < 32 → bget m1 (a + i) = bget m2 (a + i)) :
    MachineState.readWord m1 a = MachineState.readWord m2 a := by
  have hn := num_congr (a := a) 32 h
  unfold num Precompile.bytesToNatPadded at hn
  unfold MachineState.readWord
  rw [hn]

/-- Frames: memory agrees with a reference outside a set of addresses. -/
theorem num_frame {m1 m2 : ByteArray} {a n : Nat} (P : Nat → Prop)
    (hframe : ∀ k, P k → bget m1 k = bget m2 k) (hP : ∀ i, i < n → P (a + i)) :
    num m1 a n = num m2 a n :=
  num_congr n (fun i hi => hframe _ (hP i hi))

theorem readWord_frame {m1 m2 : ByteArray} {a : Nat} (P : Nat → Prop)
    (hframe : ∀ k, P k → bget m1 k = bget m2 k) (hP : ∀ i, i < 32 → P (a + i)) :
    MachineState.readWord m1 a = MachineState.readWord m2 a :=
  readWord_congr (fun i hi => hframe _ (hP i hi))

/-! ## Bits of a window -/

/-- The `j`-th most significant bit of a `k`-byte window is the bit selected by
`bitWord` at byte `j / 8`. -/
theorem num_bit (mem : ByteArray) (y k j : Nat) (hj : j < 8 * k) :
    num mem y k / 2 ^ (8 * k - j - 1) % 2 =
      (bitWord mem (y + j / 8) (j % 8)).toNat := by
  rw [bitWord_toNat mem _ _ (Nat.mod_lt _ (by norm_num))]
  have hq : j / 8 < k := by omega
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add mem y (j / 8 + 1) (k - (j / 8 + 1))
  rw [show j / 8 + 1 + (k - (j / 8 + 1)) = k by omega] at hsplit
  have htail := num_lt mem (y + (j / 8 + 1)) (k - (j / 8 + 1))
  have hpow : (256 : Nat) ^ (k - (j / 8 + 1)) = 2 ^ (8 * (k - (j / 8 + 1))) := by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul]
  have hexp : 8 * k - j - 1 = 8 * (k - (j / 8 + 1)) + (7 - j % 8) := by omega
  change num mem y k = num mem y (j / 8 + 1) * 256 ^ (k - (j / 8 + 1)) +
    num mem (y + (j / 8 + 1)) (k - (j / 8 + 1)) at hsplit
  rw [hexp, pow_add, ← Nat.div_div_eq_div_mul, hsplit, ← hpow]
  have hhigh : (num mem y (j / 8 + 1) * 256 ^ (k - (j / 8 + 1)) +
      num mem (y + (j / 8 + 1)) (k - (j / 8 + 1))) / 256 ^ (k - (j / 8 + 1)) =
      num mem y (j / 8 + 1) := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt htail,
      Nat.zero_add]
  rw [hhigh, num_succ]
  have hr : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h256 : (256 : Nat) = 2 ^ (7 - j % 8) * 2 ^ (j % 8 + 1) := by
    rw [← pow_add, show 7 - j % 8 + (j % 8 + 1) = 8 by omega]
    norm_num
  have key : (num mem y (j / 8) * 256 + bget mem (y + j / 8)) / 2 ^ (7 - j % 8) =
      bget mem (y + j / 8) / 2 ^ (7 - j % 8) + num mem y (j / 8) * 2 ^ (j % 8 + 1) := by
    rw [h256, show num mem y (j / 8) * (2 ^ (7 - j % 8) * 2 ^ (j % 8 + 1)) +
        bget mem (y + j / 8) =
      bget mem (y + j / 8) + 2 ^ (7 - j % 8) * (num mem y (j / 8) * 2 ^ (j % 8 + 1)) by ring]
    exact Nat.add_mul_div_left _ _ (by positivity)
  rw [key, Nat.add_mod]
  have heven : num mem y (j / 8) * 2 ^ (j % 8 + 1) % 2 = 0 := by
    rw [pow_succ, ← Nat.mul_assoc]
    exact Nat.mul_mod_left _ 2
  rw [heven, Nat.add_zero, Nat.mod_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC
