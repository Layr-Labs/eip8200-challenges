import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableSparse
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory StaggerTableMemory StaggerTableLayout

def zeroBytes : ByteArray := ByteArray.mk (Array.replicate 1112 (0 : UInt8))
def zeroMemory (memory : ByteArray) : ByteArray := MachineState.writeBytes memory zeroBytes 0

@[simp] theorem zeroBytes_size : zeroBytes.size = 1112 := rfl
@[simp] theorem zeroBytes_getD (i : Nat) : zeroBytes[i]?.getD 0 = 0 := by
  change (Array.replicate 1112 (0 : UInt8))[i]?.getD 0 = 0
  by_cases hi : i < 1112
  · rw [getElem?_pos _ _ (by simpa using hi)]
    simp
  · rw [getElem?_neg _ _ (by simpa using hi)]
    rfl

@[simp] theorem zeroMemory_size (memory : ByteArray) :
    (zeroMemory memory).size = max memory.size 1112 := by
  simp [zeroMemory, MachineState.writeBytes_size]

@[simp] theorem zeroMemory_getD (memory : ByteArray) (i : Nat) :
    (zeroMemory memory)[i]?.getD 0 = if i < 1112 then 0 else memory[i]?.getD 0 := by
  simp [zeroMemory, MachineState.writeBytes_getElem?_getD]

/-- Words below `2 ^ 112` (the pad-only block stores the unmasked bit lengths `n <<< 3` and
`n >>> 29`, which carry dead bits above their low 32) leave their first 18 bytes zero, so a
store never reaches the next slot 18 bytes up. -/
private theorem encoded_prefix_zero (value : UInt256) (hv : value.toNat < 2 ^ 112)
    (i : Nat) (hi : i < 18) :
    (Data.Bytes.natToBytesPadded value.toNat 32)[i]?.getD 0 = 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega)]
  have hp : (256 : Nat) ^ 14 ≤ 256 ^ (32 - 1 - i) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hv' : value.toNat < 256 ^ (32 - 1 - i) := by
    calc
      value.toNat < 2 ^ 112 := hv
      _ = 256 ^ 14 := by norm_num
      _ ≤ _ := hp
  rw [Nat.div_eq_of_lt hv']
  rfl

/-- Writes of small words cannot introduce data before their final fourteen bytes. -/
theorem getD_storeDescending_prefix_zero (memory : ByteArray) (words : Nat → UInt256)
    (first count address : Nat) (ha : address < 18 * first + 18)
    (hz : memory[address]?.getD 0 = 0)
    (hw : ∀ j, first ≤ j → j < first + count → (words j).toNat < 2 ^ 112) :
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
      if keep first then writeWord rest (18 * first) (words first) else rest

theorem storeDescending_size_ge (memory : ByteArray) (words : Nat → UInt256)
    (first count : Nat) : memory.size ≤ (storeDescending memory words first count).size := by
  cases count with
  | zero => exact Nat.le_refl _
  | succ count => rw [storeDescending_size _ _ _ _ (by omega)]; exact Nat.le_max_left _ _

/-- A zeroed table permits skipping any store whose logical word is zero. -/
theorem selected_eq_full (memory : ByteArray) (words : Nat → UInt256) (keep : Nat → Bool)
    (first count : Nat) (hend : first + count ≤ 61)
    (hw : ∀ j, first ≤ j → j < first + count → (words j).toNat < 2 ^ 112)
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

/-- Selected stores never touch bytes outside their 32-byte windows. -/
theorem getD_storeSelected_outside (memory : ByteArray) (words : Nat → UInt256)
    (keep : Nat → Bool) (first count address : Nat)
    (hout : ∀ k, first ≤ k → k < first + count →
      address < 18 * k ∨ 18 * k + 32 ≤ address) :
    (storeSelected memory words keep first count)[address]?.getD 0 =
      memory[address]?.getD 0 := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    rw [storeSelected]
    have hrest := ih (first + 1) (fun k hk hk' => hout k (by omega) (by omega))
    split
    · simp only [writeWord, MachineState.writeBytes_getElem?_getD,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      have h := hout first (by omega) (by omega)
      rw [if_neg (by omega)]
      exact hrest
    · exact hrest

theorem erase_zeroMemory (memory : ByteArray) (words : Nat → UInt256) :
    storeDescending (zeroMemory memory) words 0 61 = storeDescending memory words 0 61 := by
  apply ByteArray.ext_getElem
  · rw [storeDescending_size _ _ _ _ (by decide),
      storeDescending_size _ _ _ _ (by decide), zeroMemory_size]
    omega
  · intro address hA hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB]
    by_cases hin : address < 1112
    · exact getD_storeDescending_inside _ _ _ _ _ _ (by decide) (by omega) (by simpa using hin)
    · rw [getD_table_outside _ _ _ (by omega), getD_table_outside _ _ _ (by omega),
        zeroMemory_getD, if_neg hin]

#print axioms selected_eq_full
#print axioms getD_storeSelected_outside
#print axioms erase_zeroMemory

/-- Bytes `[14,28)` are zero as soon as the first memory word's low 144 bits are below
`2 ^ 32`.  Byte `i` sits at bits `8 * (31 - i) .. 8 * (31 - i) + 7`, which for `14 ≤ i < 28`
lies in `[32,144)` -- entirely inside the window the weakened invariant constrains. -/
theorem prefix_zero_low (memory : ByteArray)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32)
    (i : Nat) (h14 : 14 ≤ i) (hi : i < 28) : memory[i]?.getD 0 = 0 := by
  have hshift := Bytes.readWord_shift_toNat memory 0 (i + 1) (by omega)
  rw [Nat.shiftRight_eq_div_pow] at hshift
  have hsplit : (2 : Nat) ^ 144
      = 2 ^ ((32 - (i + 1)) * 8) * 2 ^ (144 - (32 - (i + 1)) * 8) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hkey : (MachineState.readWord memory 0).toNat / 2 ^ ((32 - (i + 1)) * 8) % 256
      = (MachineState.readWord memory 0).toNat % 2 ^ 144
          / 2 ^ ((32 - (i + 1)) * 8) % 256 := by
    rw [hsplit, Nat.mod_mul_right_div_self, show (256 : Nat) = 2 ^ 8 by norm_num,
      Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : 8 ≤ 144 - (32 - (i + 1)) * 8))]
  have hdiv : (MachineState.readWord memory 0).toNat % 2 ^ 144
      / 2 ^ ((32 - (i + 1)) * 8) = 0 :=
    Nat.div_eq_of_lt (lt_of_lt_of_le hlow (Nat.pow_le_pow_right (by decide) (by omega)))
  have hzero : Precompile.bytesToNatPadded memory 0 (i + 1) % 256 = 0 := by
    rw [← hshift, hkey, hdiv]
  have hs := Bytes.bytesToNatPadded_succ memory 0 i
  rw [Nat.zero_add] at hs
  have hblt : (YulSemantics.EVM.byteFrom memory.toList i).toNat < 256 :=
    (YulSemantics.EVM.byteFrom memory.toList i).toBitVec.isLt
  have hb : (YulSemantics.EVM.byteFrom memory.toList i).toNat = 0 := by omega
  have he : YulSemantics.EVM.byteFrom memory.toList i = (0 : UInt8) :=
    UInt8.toNat_inj.mp hb
  change memory.data[i]?.getD 0 = 0
  simpa only [YulSemantics.EVM.byteFrom, List.getD_eq_getElem?_getD,
    YulEvmCompiler.ByteArray.toList_eq_data, Array.getElem?_toList] using he

/-- The memory the pad block's calldata copy actually leaves: zeros from byte 28 up, with
bytes `[0,28)` untouched.  Definitionally `MachineState.writeBytes memory
PadZeroPrefix.zeroBytes 28`, but nameable from modules that do not import `PadZeroPrefix`. -/
def zeroSuffix (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes memory (ByteArray.mk (Array.replicate 1084 (0 : UInt8))) 28

private theorem suffixBytes_size :
    (ByteArray.mk (Array.replicate 1084 (0 : UInt8))).size = 1084 := rfl

private theorem suffixBytes_getD (i : Nat) :
    (ByteArray.mk (Array.replicate 1084 (0 : UInt8)))[i]?.getD 0 = 0 := by
  change (Array.replicate 1084 (0 : UInt8))[i]?.getD 0 = 0
  by_cases hi : i < 1084
  · rw [getElem?_pos _ _ (by simpa using hi)]; simp
  · rw [getElem?_neg _ _ (by simpa using hi)]; rfl

theorem zeroSuffix_size (memory : ByteArray) :
    (zeroSuffix memory).size = max memory.size 1112 := by
  rw [zeroSuffix, MachineState.writeBytes_size, suffixBytes_size, if_neg (by decide)]

/-- The machine's real pad base: zero on `[28,1112)`, the incoming memory elsewhere. -/
theorem zeroSuffix_getD (memory : ByteArray) (i : Nat) :
    (zeroSuffix memory)[i]?.getD 0 =
      if 28 ≤ i ∧ i < 1112 then 0 else memory[i]?.getD 0 := by
  rw [zeroSuffix, MachineState.writeBytes_getElem?_getD, suffixBytes_size]
  by_cases h : 28 ≤ i ∧ i < 1112
  · rw [if_pos (by omega), if_pos h, suffixBytes_getD]
  · rw [if_neg (by omega), if_neg h]

/-- Reality versus model for the pad-only block: the machine clears only from byte 28 up,
the model clears `[0,1112)`.  They are NOT equal once a previous block leaves a dual lane in
bytes 10..13, but they agree from byte 14, which is all the subsystem can observe. -/
theorem zeroSuffix_agree (memory : ByteArray)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) :
    AgreeFrom14 (zeroSuffix memory) (zeroMemory memory) := by
  refine ⟨?_, ?_⟩
  · rw [zeroSuffix, zeroMemory, MachineState.writeBytes_size, MachineState.writeBytes_size,
      if_neg (by decide), if_neg (by decide), suffixBytes_size, zeroBytes_size]
  · intro j hj
    rw [zeroSuffix, zeroMemory, MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD, suffixBytes_size, zeroBytes_size]
    simp only [suffixBytes_getD, zeroBytes_getD]
    by_cases hi : j < 28
    · rw [if_neg (by omega), if_pos (by omega), prefix_zero_low memory hlow j hj hi]
    · by_cases hend : j < 1112
      · rw [if_pos (by omega), if_pos (by omega)]
      · rw [if_neg (by omega), if_neg (by omega)]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableSparse
