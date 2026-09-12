import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableMemory
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory

/-- Actual overwrite order: higher addresses are written before lower ones. -/
def storeDescending (memory : ByteArray) (words : Nat → UInt256)
    (first : Nat) : Nat → ByteArray
  | 0 => memory
  | count + 1 => writeWord (storeDescending memory words (first + 1) count)
      (18 * first) (words first)

/-- Words above the complete 1112-byte table are unchanged. -/
theorem getD_storeDescending_outside (memory : ByteArray) (words : Nat → UInt256)
    (first count address : Nat)
    (hout : ∀ k, first ≤ k → k < first + count →
      address < 18 * k ∨ 18 * k + 32 ≤ address) :
    (storeDescending memory words first count)[address]?.getD 0 =
      memory[address]?.getD 0 := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    rw [storeDescending]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    have h := hout first (by omega) (by omega)
    rw [if_neg (by omega)]
    exact ih (first + 1) (fun k hk hk' => hout k (by omega) (by omega))

theorem getD_table_outside (memory : ByteArray) (words : Nat → UInt256)
    (address : Nat) (ha : 1112 ≤ address) :
    (storeDescending memory words 0 61)[address]?.getD 0 =
      memory[address]?.getD 0 := by
  exact getD_storeDescending_outside _ _ _ _ _ (fun k hk hk' => Or.inr (by omega))

/-- A full pair load consists of the previous slot suffix and current slot suffix. -/
theorem getD_pair (memory : ByteArray) (words : Nat → UInt256)
    (first count j k : Nat) (hfirst : first < j) (hj : j < first + count)
    (hk : k < 32) :
    (storeDescending memory words first count)[18 * j + k]?.getD 0 =
      if k < 14 then
        (Data.Bytes.natToBytesPadded (words (j - 1)).toNat 32)[18 + k]?.getD 0
      else
        (Data.Bytes.natToBytesPadded (words j).toNat 32)[k]?.getD 0 := by
  induction count generalizing first with
  | zero => omega
  | succ count ih =>
    rw [storeDescending]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases hnext : first + 1 < j
    · rw [if_neg (by omega)]
      exact ih (first + 1) hnext (by omega)
    · have hfirstEq : first = j - 1 := by omega
      by_cases hk14 : k < 14
      · rw [if_pos (by omega), if_pos hk14, hfirstEq]
        congr 2
        omega
      · rw [if_neg (by omega), if_neg hk14]
        have hc : 0 < count := by omega
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : count ≠ 0)
        rw [storeDescending]
        simp only [writeWord, MachineState.writeBytes_getElem?_getD,
          YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        rw [if_pos (by omega)]
        have hf : first + 1 = j := by omega
        rw [hf]
        congr 2
        omega

#print axioms getD_pair

/-- Low bytes of MLOAD are exactly the suffix byte decoder. -/
theorem readWord_mod_pow (memory : ByteArray) (address width : Nat)
    (hw : width ≤ 32) :
    (MachineState.readWord memory address).toNat % 256 ^ width =
      Precompile.bytesToNatPadded memory (address + (32 - width)) width := by
  have hsplit := Bytes.bytesToNatPadded_add memory address (32 - width) width
  have hsum : 32 - width + width = 32 := by omega
  rw [hsum] at hsplit
  rw [Bytes.readWord_toNat, hsplit]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero,
    Nat.zero_add, Nat.mod_mod, Nat.zero_mod]
  exact Nat.mod_eq_of_lt (Bytes.bytesToNatPadded_lt_pow _ _ _)

private theorem readWord_encoded (value : UInt256) :
    MachineState.readWord (Data.Bytes.natToBytesPadded value.toNat 32) 0 = value := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat]
  unfold Precompile.bytesToNatPadded
  have hs : (Data.Bytes.natToBytesPadded value.toNat 32).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have hr : MachineState.readPadded (Data.Bytes.natToBytesPadded value.toNat 32) 0 32 = Data.Bytes.natToBytesPadded value.toNat 32 := by
    simpa only [hs] using Memory.readPadded_zero_size (Data.Bytes.natToBytesPadded value.toNat 32)
  rw [hr]
  exact Memory.bytesToBigEndianNat_natToBytesPadded _ _
    (by exact value.val.isLt)

private theorem bytesToNatPadded_congrOffset (a b : ByteArray) (startA startB width : Nat)
    (h : ∀ i, i < width → a[startA + i]?.getD 0 = b[startB + i]?.getD 0) :
    Precompile.bytesToNatPadded a startA width = Precompile.bytesToNatPadded b startB width := by
  unfold Precompile.bytesToNatPadded
  congr 1
  apply ByteArray.ext_getElem
  · simp
  · intro i hiA hiB
    rw [← Memory.getD0_eq_getElem _ _ hiA, ← Memory.getD0_eq_getElem _ _ hiB,
      Memory.readPadded_getElem?_getD, Memory.readPadded_getElem?_getD]
    have hi : i < width := by simpa using hiA
    rw [if_pos hi, if_pos hi]
    exact h i hi

theorem read_pair (memory : ByteArray) (words : Nat → UInt256)
    (first count j : Nat) (hfirst : first < j) (hj : j < first + count)
    (hlo : (words j).toNat < 2 ^ 32) (hhi : (words (j - 1)).toNat < 2 ^ 32) :
    (MachineState.readWord (storeDescending memory words first count) (18 * j)).toNat =
      (words j).toNat + (words (j - 1)).toNat * 2 ^ 144 := by
  rw [Bytes.readWord_toNat]
  have hp := Bytes.bytesToNatPadded_add (storeDescending memory words first count) (18 * j) 14 18
  change Precompile.bytesToNatPadded (storeDescending memory words first count) (18 * j) 32 = _
  rw [show 32 = 14 + 18 by rfl, hp]
  have hupper : Precompile.bytesToNatPadded (storeDescending memory words first count) (18 * j) 14 =
      Precompile.bytesToNatPadded (Data.Bytes.natToBytesPadded (words (j - 1)).toNat 32) 18 14 := by
    apply bytesToNatPadded_congrOffset
    intro k hk
    rw [getD_pair _ _ _ _ _ _ hfirst hj (by omega), if_pos hk]
  have hlower : Precompile.bytesToNatPadded (storeDescending memory words first count) (18 * j + 14) 18 =
      Precompile.bytesToNatPadded (Data.Bytes.natToBytesPadded (words j).toNat 32) 14 18 := by
    apply bytesToNatPadded_congrOffset
    intro k hk
    have h := getD_pair memory words first count j (14 + k) hfirst hj (by omega)
    rw [if_neg (by omega : ¬14 + k < 14)] at h
    simpa only [← Nat.add_assoc] using h
  rw [hupper, hlower]
  have hupperNat := readWord_mod_pow (Data.Bytes.natToBytesPadded (words (j - 1)).toNat 32) 0 14 (by omega)
  have hlowerNat := readWord_mod_pow (Data.Bytes.natToBytesPadded (words j).toNat 32) 0 18 (by omega)
  rw [readWord_encoded] at hupperNat hlowerNat
  norm_num only at hupperNat hlowerNat
  rw [← hupperNat, ← hlowerNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  norm_num only
  omega

#print axioms read_pair

theorem storeDescending_size (memory : ByteArray) (words : Nat → UInt256)
    (first count : Nat) (hc : 0 < count) :
    (storeDescending memory words first count).size =
      max memory.size (18 * (first + count - 1) + 32) := by
  induction count generalizing first with
  | zero => omega
  | succ count ih =>
    rw [storeDescending, writeWord_size]
    by_cases hzero : count = 0
    · subst count
      simp only [storeDescending]
      congr 1
    · rw [ih (first + 1) (by omega)]
      have heq : first + 1 + count - 1 = first + (count + 1) - 1 := by omega
      rw [heq]
      omega

theorem getD_storeDescending_inside (a b : ByteArray) (words : Nat → UInt256)
    (first count address : Nat) (hc : 0 < count)
    (hlo : 18 * first ≤ address) (hhi : address < 18 * (first + count - 1) + 32) :
    (storeDescending a words first count)[address]?.getD 0 =
      (storeDescending b words first count)[address]?.getD 0 := by
  induction count generalizing first with
  | zero => omega
  | succ count ih =>
    rw [storeDescending, storeDescending]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases hin : 18 * first ≤ address ∧ address < 18 * first + 32
    · rw [if_pos hin, if_pos hin]
    · rw [if_neg hin, if_neg hin]
      exact ih (first + 1) (by omega) (by omega) (by omega)

theorem read_table_outside (memory : ByteArray) (words : Nat → UInt256)
    (address : Nat) (ha : 1112 ≤ address) :
    MachineState.readWord (storeDescending memory words 0 61) address =
      MachineState.readWord memory address := by
  unfold MachineState.readWord
  congr 2
  apply Memory.readPadded_congr
  intro i hi
  exact getD_table_outside memory words _ (by omega)

/-- Two packed source words live here only until every source is on the stack. -/
def scratchMemory (memory : ByteArray) (low high : UInt256) : ByteArray :=
  writeWord (writeWord memory 64 high) 32 low

theorem erase_scratch (memory : ByteArray) (words : Nat → UInt256)
    (low high : UInt256) :
    storeDescending (scratchMemory memory low high) words 0 61 =
      storeDescending memory words 0 61 := by
  apply ByteArray.ext_getElem
  · rw [storeDescending_size _ _ _ _ (by omega),
      storeDescending_size _ _ _ _ (by omega)]
    simp only [scratchMemory, writeWord_size]
    omega
  · intro address hA hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB]
    by_cases hin : address < 1112
    · exact getD_storeDescending_inside _ _ _ _ _ _ (by omega) (by omega) (by simpa using hin)
    · rw [getD_table_outside _ _ _ (by omega), getD_table_outside _ _ _ (by omega)]
      simp only [scratchMemory, writeWord, MachineState.writeBytes_getElem?_getD,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      rw [if_neg (by omega), if_neg (by omega)]

#print axioms storeDescending_size
#print axioms read_table_outside
#print axioms erase_scratch
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableMemory
