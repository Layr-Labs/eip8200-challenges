import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableLayout
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableSparse
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory PairTableMemory PairTableLayout

def zeroBytes : ByteArray := ByteArray.mk (Array.replicate 802 (0 : UInt8))
def zeroMemory (memory : ByteArray) : ByteArray := MachineState.writeBytes memory zeroBytes 0

@[simp] theorem zeroBytes_size : zeroBytes.size = 802 := rfl
@[simp] theorem zeroBytes_getD (i : Nat) : zeroBytes[i]?.getD 0 = 0 := by
  change (Array.replicate 802 (0 : UInt8))[i]?.getD 0 = 0
  by_cases hi : i < 802
  · rw [getElem?_pos _ _ (by simpa using hi)]
    simp
  · rw [getElem?_neg _ _ (by simpa using hi)]
    rfl

@[simp] theorem zeroMemory_size (memory : ByteArray) :
    (zeroMemory memory).size = max memory.size 802 := by
  simp [zeroMemory, MachineState.writeBytes_size]

@[simp] theorem zeroMemory_getD (memory : ByteArray) (i : Nat) :
    (zeroMemory memory)[i]?.getD 0 = if i < 802 then 0 else memory[i]?.getD 0 := by
  simp [zeroMemory, MachineState.writeBytes_getElem?_getD]

private theorem encoded_prefix_zero (value : UInt256) (hv : value.toNat < 2 ^ 32)
    (i : Nat) (hi : i < 28) :
    (Data.Bytes.natToBytesPadded value.toNat 32)[i]?.getD 0 = 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega)]
  have hp : (256 : Nat) ^ 4 ≤ 256 ^ (32 - 1 - i) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hv' : value.toNat < 256 ^ (32 - 1 - i) := by
    calc
      value.toNat < 2 ^ 32 := hv
      _ = 256 ^ 4 := by norm_num
      _ ≤ _ := hp
  rw [Nat.div_eq_of_lt hv']
  rfl

/-- Writes of small words cannot introduce data before their final four bytes. -/
theorem getD_storeDescending_prefix_zero (memory : ByteArray) (words : Nat → UInt256)
    (first count address : Nat) (ha : address < 10 * first + 28)
    (hz : memory[address]?.getD 0 = 0)
    (hw : ∀ j, first ≤ j → j < first + count → (words j).toNat < 2 ^ 32) :
    (storeDescending memory words first count)[address]?.getD 0 = 0 := by
  induction count generalizing first with
  | zero => exact hz
  | succ count ih =>
    rw [storeDescending]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split
    · exact encoded_prefix_zero _ (hw first (by omega) (by omega)) _ (by omega)
    · exact ih (first + 1) (by omega) (fun j hj hj' => hw j (by omega) (by omega))

def storeSelected (memory : ByteArray) (words : Nat → UInt256) (keep : Nat → Bool)
    (first : Nat) : Nat → ByteArray
  | 0 => memory
  | count + 1 =>
      let rest := storeSelected memory words keep (first + 1) count
      if keep first then writeWord rest (10 * first) (words first) else rest

theorem storeDescending_size_ge (memory : ByteArray) (words : Nat → UInt256)
    (first count : Nat) : memory.size ≤ (storeDescending memory words first count).size := by
  cases count with
  | zero => exact Nat.le_refl _
  | succ count => rw [storeDescending_size _ _ _ _ (by omega)]; exact Nat.le_max_left _ _

/-- A zeroed table permits skipping any store whose logical word is zero. -/
theorem selected_eq_full (memory : ByteArray) (words : Nat → UInt256) (keep : Nat → Bool)
    (first count : Nat) (hend : first + count ≤ 78)
    (hw : ∀ j, first ≤ j → j < first + count → (words j).toNat < 2 ^ 32)
    (hskip : ∀ j, first ≤ j → j < first + count → keep j = false → words j = UInt256.ofNat 0) :
    storeSelected (zeroMemory memory) words keep first count =
      storeDescending (zeroMemory memory) words first count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    rw [storeSelected, storeDescending]
    rw [ih (first + 1) (by omega)
      (fun j hj hj' => hw j (by omega) (by omega))
      (fun j hj hj' hk => hskip j (by omega) (by omega) hk)]
    split
    · rfl
    · rename_i hkeep
      have hk : keep first = false := by simpa using hkeep
      rw [hskip first (by omega) (by omega) hk]
      symm
      apply writeWord_zero_noop
      · have hs := storeDescending_size_ge (zeroMemory memory) words (first + 1) count
        rw [zeroMemory_size] at hs
        omega
      · intro i hi
        apply getD_storeDescending_prefix_zero
        · omega
        · rw [zeroMemory_getD, if_pos (by omega)]
        · exact fun j hj hj' => hw j (by omega) (by omega)

theorem erase_zeroMemory (memory : ByteArray) (words : Nat → UInt256) :
    storeDescending (zeroMemory memory) words 0 78 = storeDescending memory words 0 78 := by
  apply ByteArray.ext_getElem
  · rw [storeDescending_size _ _ _ _ (by decide),
      storeDescending_size _ _ _ _ (by decide), zeroMemory_size]
    omega
  · intro address hA hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB]
    by_cases hin : address < 802
    · exact getD_storeDescending_inside _ _ _ _ _ _ (by decide) (by omega) (by simpa using hin)
    · rw [getD_table_outside _ _ _ (by omega), getD_table_outside _ _ _ (by omega),
        zeroMemory_getD, if_neg hin]

#print axioms selected_eq_full
#print axioms erase_zeroMemory
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableSparse
