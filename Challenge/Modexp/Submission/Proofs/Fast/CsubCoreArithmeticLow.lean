import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreCsubTail
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
attribute [local simp] jumpDestCopyResume
/-- The value of the low `j` limbs of the `n`-limb big-endian block at `ptr`
(limb `k` sits at `ptr + 32 * (n - 1 - k)`). -/
def lowValue (memory : ByteArray) (ptr n j : Nat) : Nat :=
  Nat.ofDigits Limbs.radix ((List.range j).map fun k =>
    (MachineState.readWord memory (ptr + 32 * (n - 1 - k))).toNat)

@[simp] theorem lowValue_zero (memory : ByteArray) (ptr n : Nat) :
    lowValue memory ptr n 0 = 0 := by
  simp [lowValue]

theorem lowValue_succ (memory : ByteArray) (ptr n j : Nat) :
    lowValue memory ptr n (j + 1) =
      lowValue memory ptr n j +
        (MachineState.readWord memory (ptr + 32 * (n - 1 - j))).toNat *
          Limbs.radix ^ j := by
  simp only [lowValue, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, Nat.ofDigits_append, List.length_map, List.length_range,
    Nat.ofDigits_singleton]
  ring

theorem lowValue_full (memory : ByteArray) (ptr n : Nat) :
    lowValue memory ptr n n =
      Nat.ofDigits Limbs.radix (Model.fastLimbs memory ptr n) := rfl

theorem lowValue_congr {a b : ByteArray} {ptr n j : Nat}
    (h : ∀ k, k < j → MachineState.readWord a (ptr + 32 * (n - 1 - k)) =
      MachineState.readWord b (ptr + 32 * (n - 1 - k))) :
    lowValue a ptr n j = lowValue b ptr n j := by
  unfold lowValue
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [h k (by simpa using hk)]

theorem lowValue_lt (memory : ByteArray) (ptr n j : Nat) :
    lowValue memory ptr n j < Limbs.radix ^ j := by
  have hdigits : ∀ d ∈ (List.range j).map (fun k =>
      (MachineState.readWord memory (ptr + 32 * (n - 1 - k))).toNat),
      d < Limbs.radix := by
    intro d hd
    simp only [List.mem_map] at hd
    rcases hd with ⟨k, _, rfl⟩
    exact (MachineState.readWord memory (ptr + 32 * (n - 1 - k))).val.isLt
  have h := Nat.ofDigits_lt_base_pow_length Limbs.radix_gt_one hdigits
  simpa [lowValue] using h

/-- A block always represents the value of its own limbs. -/
theorem fastRepresents_lowValue (memory : ByteArray) (ptr n : Nat) :
    Model.FastRepresents memory ptr n (lowValue memory ptr n n) :=
  (Model.fastRepresents_iff_value (lowValue_lt memory ptr n n)).2
    (lowValue_full memory ptr n).symm

/-! ## The limb steps -/

theorem or_of_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b = max a b := by
  interval_cases a <;> interval_cases b <;> decide

/-- One `ADDMOD` limb: the stored word and the two overflow tests realise the
three-term natural sum with its carry. -/
theorem addLimb_spec (x y c : UInt256) (hc : c.toNat ≤ 1) :
    (c + (x + y)).toNat + Limbs.radix *
        (UInt256.lor (UInt256.lt (c + (x + y)) c) (UInt256.lt (x + y) x)).toNat =
      x.toNat + y.toNat + c.toNat ∧
    (UInt256.lor (UInt256.lt (c + (x + y)) c) (UInt256.lt (x + y) x)).toNat ≤ 1 := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have hy : y.toNat < 2 ^ 256 := y.val.isLt
  have h1 : (UInt256.lt (c + (x + y)) c).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  have h2 : (UInt256.lt (x + y) x).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  rw [Challenge.EvmProof.Word.word_toNat_lor, or_of_le_one h1 h2]
  simp only [Challenge.EvmProof.Word.word_toNat_lt,
    Challenge.EvmProof.Word.word_toNat_add, Limbs.radix]
  constructor
  · split_ifs <;> omega
  · split_ifs <;> omega

/-- One `CSUB` limb: the stored word and the two borrow tests realise the
three-term natural difference with its borrow. -/
theorem subLimb_spec (x y b : UInt256) (hb : b.toNat ≤ 1) :
    (x - y - b).toNat + y.toNat + b.toNat =
      x.toNat + Limbs.radix *
        (UInt256.lor (UInt256.lt x y) (UInt256.lt (x - y) b)).toNat ∧
    (UInt256.lor (UInt256.lt x y) (UInt256.lt (x - y) b)).toNat ≤ 1 := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have hy : y.toNat < 2 ^ 256 := y.val.isLt
  have h1 : (UInt256.lt x y).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  have h2 : (UInt256.lt (x - y) b).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  rw [Challenge.EvmProof.Word.word_toNat_lor, or_of_le_one h1 h2]
  simp only [Challenge.EvmProof.Word.word_toNat_lt,
    Challenge.EvmProof.Word.word_toNat_sub_cond, Limbs.radix]
  constructor
  · split_ifs <;> omega
  · split_ifs <;> omega

/-- A 32-byte write outside a 32-byte read window is invisible. -/
theorem readWord_write_disjoint (memory : ByteArray) (w addr wr : Nat)
    (hdisj : addr + 32 ≤ wr ∨ wr + 32 ≤ addr) :
    MachineState.readWord (MachineState.writeBytes memory
      (Data.Bytes.natToBytesPadded w 32) wr) addr =
      MachineState.readWord memory addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact hdisj


/-! ## The `ADDMOD` loop invariant -/

/-- The algebraic core of one carry step. -/
theorem am_algebra (L A B P R T F xa xb c : Nat)
    (hlimb : T + R * F = xa + xb + c) (hinv : L + c * P = A + B) :
    L + T * P + F * (P * R) = A + xa * P + (B + xb * P) := by
  have h1 : L + T * P + F * (P * R) = L + (T + R * F) * P := by ring
  rw [h1, hlimb]
  have h2 : L + (xa + xb + c) * P = L + c * P + (xa * P + xb * P) := by ring
  rw [h2, hinv]
  ring

/-- The algebraic core of one borrow step. -/
theorem cs_algebra (D M T P R d2 md t b F : Nat)
    (hlimb : d2 + md + b = t + R * F) (hinv : D + M = T + b * P) :
    D + d2 * P + (M + md * P) = T + t * P + F * (P * R) := by
  have h1 : D + d2 * P + (M + md * P) = D + M + (d2 + md) * P := by ring
  rw [h1, hinv]
  have h2 : T + b * P + (d2 + md) * P = T + (d2 + md + b) * P := by ring
  rw [h2, hlimb]
  ring

/-- The `ADDMOD` loop only writes into the `t` block. -/
theorem amStep_readWord_disjoint (memory : ByteArray) (pa pb n addr : Nat)
    (_hn : 1 ≤ n) (hdisj : addr + 32 ≤ 2112 ∨ 2112 + 32 * n ≤ addr) :
    ∀ j, j ≤ n → MachineState.readWord (amStep memory pa pb n j).memory addr =
      MachineState.readWord memory addr := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (amStep memory pa pb n (j + 1)).memory addr =
          MachineState.readWord (amStep memory pa pb n j).memory addr := by
        simp only [amStep]
        exact readWord_write_disjoint _ _ _ _ (by omega)
      rw [hstep, ih (by omega)]

/-- Step `j` does not disturb the limbs below `j`. -/
theorem amStep_lowValue_stable (memory : ByteArray) (pa pb n j : Nat) (hj : j < n) :
    lowValue (amStep memory pa pb n (j + 1)).memory 2112 n j =
      lowValue (amStep memory pa pb n j).memory 2112 n j := by
  apply lowValue_congr
  intro k hk
  simp only [amStep]
  exact readWord_write_disjoint _ _ _ _ (by omega)

theorem amStep_readWord_new (memory : ByteArray) (pa pb n j : Nat) :
    MachineState.readWord (amStep memory pa pb n (j + 1)).memory
        (2112 + 32 * (n - 1 - j)) =
      (amStep memory pa pb n j).flag +
        (MachineState.readWord (amStep memory pa pb n j).memory (pa + 32 * (n - 1 - j)) +
          MachineState.readWord (amStep memory pa pb n j).memory
            (pb + 32 * (n - 1 - j))) := by
  simp only [amStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem amStep_flag_succ (memory : ByteArray) (pa pb n j : Nat) :
    (amStep memory pa pb n (j + 1)).flag =
      UInt256.lor
        (UInt256.lt ((amStep memory pa pb n j).flag +
          (MachineState.readWord (amStep memory pa pb n j).memory (pa + 32 * (n - 1 - j)) +
            MachineState.readWord (amStep memory pa pb n j).memory (pb + 32 * (n - 1 - j))))
          (amStep memory pa pb n j).flag)
        (UInt256.lt
          (MachineState.readWord (amStep memory pa pb n j).memory (pa + 32 * (n - 1 - j)) +
            MachineState.readWord (amStep memory pa pb n j).memory (pb + 32 * (n - 1 - j)))
          (MachineState.readWord (amStep memory pa pb n j).memory
            (pa + 32 * (n - 1 - j)))) := by
  simp only [amStep]


end Challenge.Modexp.Submission.Proofs.Fast.Csub
