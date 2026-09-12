import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionRecurrence
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanMask

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAccumulator
open EvmSemantics EvmSemantics.EVM
open RecognitionRecurrence TailProjection PatternedInputData

def Allowed (n : Nat) : Prop :=
  n = 1 ∨ n = 31 ∨ n = 32 ∨ n = 55 ∨ n = 56 ∨ n = 63 ∨ n = 64 ∨
  n = 65 ∨ n = 119 ∨ n = 120 ∨ n = 128 ∨ n = 256 ∨ n = 376 ∨ n = 1000

theorem allowed_bounds (n : Nat) (hn : Allowed n) : 0 < n ∧ n ≤ 1000 := by
  unfold Allowed at hn
  omega

def reference (n : Nat) : ByteArray := patternedInput.extract 0 n

theorem reference_size (n : Nat) (hn : n ≤ 1000) : (reference n).size = n := by
  simp [reference, patternedInput_size, Nat.min_eq_left hn]

theorem bytesToNatPadded_reference (n off width : Nat) (hn : n ≤ 1000)
    (hfit : off + width ≤ n) :
    Precompile.bytesToNatPadded (reference n) off width =
      Precompile.bytesToNatPadded patternedInput off width := by
  apply (bytesToNatPadded_eq_iff (reference n) patternedInput off width).mpr
  intro i hi
  have hsmall : off + i < n := by omega
  rw [byteFrom_getElem (reference n) (off + i) (by rw [reference_size n hn]; omega),
    byteFrom_getElem patternedInput (off + i) (by rw [patternedInput_size]; omega)]
  simp only [reference, ByteArray.getElem_extract, Nat.zero_add]

def count (n : Nat) : Nat := (n + 31) / 32

def shift (n k : Nat) : UInt256 := UInt256.ofNat ((32 - min 32 (n - 32*k)) * 8)

theorem projection (n k : Nat) (hn : Allowed n) (hk : k < count n) :
    UInt256.shiftRight (compareWord k) (shift n k) =
      UInt256.shiftRight (MachineState.readWord (reference n) (32*k)) (shift n k) := by
  have hb := allowed_bounds n hn
  have hk32 : k < 32 := by unfold count at hk; omega
  by_cases hlast : k = 31
  · subst k
    have hn1000 : n = 1000 := by unfold Allowed at hn; unfold count at hk; omega
    subst n
    have hr : reference 1000 = patternedInput := by
      simp [reference, ← patternedInput_size]
    rw [hr, PatternedWordLogic.readWord_patterned]
    change UInt256.shiftRight (baseWord 31) (UInt256.ofNat 192) = _
    exact partial31
  · rw [compareWord_eq_expected k (by omega), ← PatternedWordLogic.readWord_patterned]
    have hp : 0 < min 32 (n - 32*k) := by unfold count at hk; omega
    have hw : min 32 (n - 32*k) ≤ 32 := Nat.min_le_left _ _
    unfold shift
    rw [Challenge.EvmProof.Bytes.shiftRight_readWord patternedInput (32*k) _ hp hw,
      Challenge.EvmProof.Bytes.shiftRight_readWord (reference n) (32*k) _ hp hw,
      bytesToNatPadded_reference n (32*k) _ hb.2 (by omega)]

def allAcc (input : ByteArray) (n : Nat) : UInt256 :=
  guardedAcc input compareWord (shift n) (count n)

theorem allAcc_zero_iff (input : ByteArray) (n : Nat) (hn : Allowed n)
    (hsize : input.size = n) : allAcc input n = 0 ↔ input = reference n := by
  have hb := allowed_bounds n hn
  have hs : input.size = (reference n).size := by rw [reference_size n hb.2]; exact hsize
  have hc : (reference n).size ≤ 32 * count n := by
    rw [reference_size n hb.2]; unfold count; omega
  have h := guardedAcc_zero_iff_eq input (reference n) compareWord (count n) hs hc
    (by
      intro k hk
      rw [reference_size n hb.2]
      exact projection n k hn hk)
  change guardedAcc input compareWord
    (fun j => UInt256.ofNat ((32 - min 32 (n - 32*j)) * 8)) (count n) = 0 ↔ _
  rw [reference_size n hb.2] at h
  exact h

private theorem shr_zero (x : UInt256) : UInt256.shiftRight x 0 = x := by
  apply PairedLaneUInt256Bridge.bits_injective
  change PairedLaneUInt256Bridge.bits (UInt256.shiftRight x (UInt256.ofNat 0)) =
    PairedLaneUInt256Bridge.bits x
  rw [PairedLaneUInt256Bridge.bits_shr x 0 (by decide)]
  simp

def fullAcc (input : ByteArray) : Nat → UInt256
  | 0 => 0
  | k + 1 => UInt256.lor
      (UInt256.xor (MachineState.readWord input (32*k)) (compareWord k))
      (fullAcc input k)

theorem fullAcc_eq_guarded (input : ByteArray) (n k : Nat) (hk : k ≤ n / 32) :
    fullAcc input k = guardedAcc input compareWord (shift n) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [fullAcc, guardedAcc, ih (by omega)]
    have hs : shift n k = 0 := by
      unfold shift
      have hm : min 32 (n - 32*k) = 32 := Nat.min_eq_left (by omega)
      rw [hm]
      rfl
    rw [hs, shr_zero]

theorem allowed_partial (n : Nat) (hn : Allowed n) (hp : n % 32 ≠ 0) :
    boundary (n / 32) = false := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [boundary] at *

def resultAcc (input : ByteArray) (n : Nat) : UInt256 :=
  if n % 32 = 0 then fullAcc input (n / 32)
  else UInt256.lor
    (UInt256.shiftRight
      (UInt256.xor (MachineState.readWord input (32*(n/32))) (baseWord (n/32)))
      (UInt256.ofNat (256 - 8*(n-32*(n/32)))))
    (fullAcc input (n/32))

theorem resultAcc_eq_allAcc (input : ByteArray) (n : Nat) (hn : Allowed n) :
    resultAcc input n = allAcc input n := by
  unfold resultAcc allAcc
  split
  · rename_i hmod
    have hc : count n = n / 32 := by unfold count; omega
    rw [hc]
    exact fullAcc_eq_guarded input n (n / 32) (by omega)
  · rename_i hmod
    have hc : count n = n / 32 + 1 := by unfold count; omega
    have hb := allowed_partial n hn hmod
    have hs : shift n (n/32) = UInt256.ofNat (256 - 8*(n-32*(n/32))) := by
      unfold shift
      have hm : min 32 (n-32*(n/32)) = n-32*(n/32) := Nat.min_eq_right (by omega)
      rw [hm]
      congr 1
      omega
    rw [hc, guardedAcc, hs, compareWord, hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [fullAcc_eq_guarded input n (n/32) (by omega)]

theorem resultAcc_zero_iff (input : ByteArray) (n : Nat) (hn : Allowed n)
    (hsize : input.size = n) : resultAcc input n = 0 ↔ input = reference n := by
  rw [resultAcc_eq_allAcc input n hn]
  exact allAcc_zero_iff input n hn hsize

#print axioms resultAcc_eq_allAcc
#print axioms resultAcc_zero_iff

#print axioms bytesToNatPadded_reference
#print axioms projection
#print axioms allAcc_zero_iff
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAccumulator
