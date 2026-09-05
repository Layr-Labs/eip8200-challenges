import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word
import Challenge.Modexp.Submission.Proofs.Limbs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory

open EvmSemantics
open Challenge.EvmProof.Memory
open Challenge.Modexp.Submission.Proofs.Limbs

/-- Copy low to high. Each store reads the next word from current memory. -/
def shiftProgress (memory : ByteArray) (t : Nat) : Nat → ByteArray
  | 0 => memory
  | j + 1 =>
      let current := shiftProgress memory t j
      let value := MachineState.readWord current (t + 32 * (j + 1))
      MachineState.writeBytes current (Data.Bytes.natToBytesPadded value.toNat 32)
        (t + 32 * j)

/-- Shift the n+2-word scratch range down one word, then clear its top word. -/
def shiftDown (memory : ByteArray) (t n : Nat) : ByteArray :=
  MachineState.writeBytes (shiftProgress memory t (n + 1))
    (Data.Bytes.natToBytesPadded 0 32) (t + 32 * (n + 1))

private theorem padded_word_size (value : Nat) :
    (Data.Bytes.natToBytesPadded value 32).size = 32 := by
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

/-- Copied limbs contain the old next limb; all later limbs are still old. -/
theorem shiftProgress_readWord (memory : ByteArray) (t j k : Nat) :
    MachineState.readWord (shiftProgress memory t j) (t + 32 * k) =
      if k < j then MachineState.readWord memory (t + 32 * (k + 1))
      else MachineState.readWord memory (t + 32 * k) := by
  induction j generalizing k with
  | zero => simp [shiftProgress]
  | succ j ih =>
      rw [shiftProgress]
      by_cases hkj : k = j
      · subst k
        rw [readWord_writeWord, ih]
        simp
      · rw [readWord_writeBytes_disjoint]
        · rw [ih]
          have hlt : (k < j + 1) ↔ k < j := by omega
          simp only [hlt]
        · rw [padded_word_size]
          omega

/-- The next source word has not been overwritten by any earlier store. -/
theorem shiftProgress_source (memory : ByteArray) (t j : Nat) :
    MachineState.readWord (shiftProgress memory t j) (t + 32 * (j + 1)) =
      MachineState.readWord memory (t + 32 * (j + 1)) := by
  rw [shiftProgress_readWord, if_neg (by omega)]

/-- Zero-padded bytes outside the stores are unchanged, including past size. -/
theorem shiftProgress_byte_outside (memory : ByteArray) (t j a : Nat) :
    a < t ∨ t + 32 * j ≤ a →
    (shiftProgress memory t j)[a]?.getD 0 = memory[a]?.getD 0 := by
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hout
      rw [shiftProgress, MachineState.writeBytes_getElem?_getD, padded_word_size,
        if_neg (by omega)]
      exact ih (by omega)

/-- The final clear store does not change any copied limb. -/
theorem shiftDown_readWord (memory : ByteArray) (t n k : Nat) (hk : k < n + 1) :
    MachineState.readWord (shiftDown memory t n) (t + 32 * k) =
      MachineState.readWord memory (t + 32 * (k + 1)) := by
  rw [shiftDown, readWord_writeBytes_disjoint]
  · rw [shiftProgress_readWord, if_pos hk]
  · left
    omega

/-- The last limb in the n+2-word range is cleared. -/
theorem shiftDown_top (memory : ByteArray) (t n : Nat) :
    MachineState.readWord (shiftDown memory t n) (t + 32 * (n + 1)) = 0 := by
  rw [shiftDown, readWord_writeBytes_of_lt _ _ _ (by norm_num)]
  rfl

/-- The final list drops the old low limb and appends one zero limb. -/
theorem shiftDown_memoryLimbs (memory : ByteArray) (t n : Nat) :
    memoryLimbs (shiftDown memory t n) t (n + 2) =
      (memoryLimbs memory t (n + 2)).drop 1 ++ [0] := by
  have hdrop : (memoryLimbs memory t (n + 2)).drop 1 =
      (List.range (n + 1)).map
        (fun k => (MachineState.readWord memory (t + 32 * (k + 1))).toNat) := by
    unfold memoryLimbs
    rw [List.range_succ_eq_map]
    simp
  rw [hdrop]
  unfold memoryLimbs
  rw [List.range_succ, List.map_append]
  simp only [List.map_singleton, shiftDown_top]
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [shiftDown_readWord memory t n k (List.mem_range.mp hk)]

/-- Division discards the low limb; no low-limb-zero premise is needed. -/
theorem shiftDown_value (memory : ByteArray) (t n : Nat) :
    Nat.ofDigits radix (memoryLimbs (shiftDown memory t n) t (n + 2)) =
      Nat.ofDigits radix (memoryLimbs memory t (n + 2)) / radix := by
  rw [shiftDown_memoryLimbs, Nat.ofDigits_append_zero, List.drop_one]
  exact (Nat.ofDigits_div_eq_ofDigits_tail radix_pos (memoryLimbs memory t (n + 2))
    (fun _ hdigit => memoryLimb_lt memory t (n + 2) hdigit)).symm

/-- All bytes outside the n+2-word write range retain their padded value. -/
theorem shiftDown_byte_outside (memory : ByteArray) (t n a : Nat)
    (hout : a < t ∨ t + 32 * (n + 2) ≤ a) :
    (shiftDown memory t n)[a]?.getD 0 = memory[a]?.getD 0 := by
  rw [shiftDown, MachineState.writeBytes_getElem?_getD, padded_word_size,
    if_neg (by omega)]
  exact shiftProgress_byte_outside memory t (n + 1) a (by omega)

/-- A word-address sum denotes the natural address when the full range fits. -/
theorem limbAddress_toNat (t count k : Nat)
    (hfit : t + 32 * count ≤ radix) (hk : k < count) :
    (UInt256.ofNat t + UInt256.ofNat (32 * k)).toNat = t + 32 * k := by
  rw [Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  unfold radix at hfit
  omega

/-- The current-memory source equality also holds for explicitly fitted words. -/
theorem shiftProgress_source_wordAddress (memory : ByteArray) (t j : Nat)
    (hfit : t + 32 * (j + 2) ≤ radix) :
    MachineState.readWord (shiftProgress memory t j)
        (UInt256.ofNat t + UInt256.ofNat (32 * (j + 1))).toNat =
      MachineState.readWord memory
        (UInt256.ofNat t + UInt256.ofNat (32 * (j + 1))).toNat := by
  rw [limbAddress_toNat t (j + 2) (j + 1) hfit (by omega)]
  exact shiftProgress_source memory t j

/-- Explicit fit connects the natural copy result to UInt256 pointer sums. -/
theorem shiftDown_readWord_wordAddress (memory : ByteArray) (t n k : Nat)
    (hfit : t + 32 * (n + 2) ≤ radix) (hk : k < n + 1) :
    MachineState.readWord (shiftDown memory t n)
        (UInt256.ofNat t + UInt256.ofNat (32 * k)).toNat =
      MachineState.readWord memory
        (UInt256.ofNat t + UInt256.ofNat (32 * (k + 1))).toNat := by
  rw [limbAddress_toNat t (n + 2) k hfit (by omega),
    limbAddress_toNat t (n + 2) (k + 1) hfit (by omega)]
  exact shiftDown_readWord memory t n k hk

end Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory
