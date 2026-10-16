import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAccumulator
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralModel
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PatternedWordData RecognitionAccumulator TailProjection

def full (input : ByteArray) : Nat → UInt256
  | 0 => 0
  | k+1 => UInt256.lor (UInt256.xor (MachineState.readWord input (32*k)) (expectedWordAt k)) (full input k)
def diff (input : ByteArray) (k : Nat) : UInt256 :=
  UInt256.xor (MachineState.readWord input (32*k)) (expectedWordAt k)
def last (n : Nat) : Nat := (n-1)/32
def result (input : ByteArray) (n : Nat) : UInt256 :=
  UInt256.lor (UInt256.shiftRight (diff input (last n))
    (UInt256.ofNat ((32*(last n+1)-n)*8))) (full input (last n))

private theorem shr0 (x : UInt256) : UInt256.shiftRight x 0 = x := by
  apply Word.word_ext
  change (UInt256.shiftRight x (UInt256.ofNat 0)).toNat = x.toNat
  rw [Word.shiftRight_toNat x (by decide)]
  simp only [Nat.shiftRight_zero]

theorem full_eq_guarded (input : ByteArray) (n k : Nat) (hk : k ≤ n/32) :
    full input k = guardedAcc input expectedWordAt (shift n) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [full, guardedAcc, ih (by omega)]
    have hs : shift n k = 0 := by
      unfold shift
      rw [Nat.min_eq_left (by omega : 32 ≤ n-32*k)]
      rfl
    rw [hs, shr0]

theorem result_eq_guarded (input : ByteArray) (n : Nat) (hn : 0 < n) :
    result input n = guardedAcc input expectedWordAt (shift n) (count n) := by
  have hc : count n = last n + 1 := by unfold count last; omega
  have hk : last n ≤ n/32 := by unfold last; omega
  have hs : shift n (last n) = UInt256.ofNat ((32*(last n+1)-n)*8) := by
    unfold shift last
    rw [Nat.min_eq_right (by omega : n-32*((n-1)/32) ≤ 32)]
    congr 1
    omega
  rw [hc, guardedAcc, hs, ← full_eq_guarded input n _ hk]
  rfl

theorem projection (n k : Nat) (hn : Allowed n) (hk : k < count n) :
    UInt256.shiftRight (expectedWordAt k) (shift n k) =
      UInt256.shiftRight (MachineState.readWord (reference n) (32*k)) (shift n k) := by
  have hb := allowed_bounds n hn
  have hk32 : k < 32 := by unfold count at hk; omega
  by_cases he : k = 31
  · subst k
    have h1000 : n = 1000 := by unfold Allowed at hn; unfold count at hk; omega
    subst n
    have hr : reference 1000 = PatternedInputData.patternedInput := by
      simp [reference, ← PatternedInputData.patternedInput_size]
    rw [hr, PatternedWordLogic.readWord_patterned]
  · rw [← RecognitionRecurrence.compareWord_eq_expected k (by omega)]
    exact RecognitionAccumulator.projection n k hn hk

theorem result_zero_iff (input : ByteArray) (n : Nat) (hn : Allowed n)
    (hsize : input.size = n) : result input n = 0 ↔ input = reference n := by
  have hb := allowed_bounds n hn
  rw [result_eq_guarded input n hb.1]
  have hs : input.size = (reference n).size := by rw [reference_size n hb.2]; exact hsize
  have hc : (reference n).size ≤ 32*count n := by rw [reference_size n hb.2]; unfold count; omega
  have h := guardedAcc_zero_iff_eq input (reference n) expectedWordAt (count n) hs hc (by
    intro k hk
    rw [reference_size n hb.2]
    exact projection n k hn hk)
  rw [reference_size n hb.2] at h
  exact h
#print axioms result_zero_iff
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralModel
