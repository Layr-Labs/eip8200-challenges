import Challenge.Modexp.Submission.Proofs.R5.TailRun
import Challenge.Modexp.Submission.Proofs.R5.NormMath
import Challenge.Modexp.Submission.Proofs.R5.PrologueMeaning
import Challenge.Modexp.Submission.Proofs.Cycle.Packing
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000
set_option exponentiation.threshold 4096

/-!
# The r5 tail (meaning): normalization and the returned bytes

* Normalization: from digits with value `T < 2N` the rounds end at `r5_done` with digits of
  value `T % N` (at most one subtraction; the second round always stops).
* Pack: `r5_done` writes the leader's `Packing.outputWord`s (with `lor` operands swapped) to
  0x00..0x80, so the 128 returned bytes are `natToBytes (T % N) 128`.
-/

namespace CycleSubmission.R5.TailMeaning
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs
open CycleSubmission.R5.ExecNorm CycleSubmission.R5.TailRun CycleSubmission.R5.PrologueMeaning

/-- Five digits as the leader's digit function (zero above). -/
def dig (a0 a1 a2 a3 a4 : UInt256) : Nat → UInt256
  | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4 | _ => UInt256.ofNat 0

def val5 (a0 a1 a2 a3 a4 : UInt256) : Nat :=
  a0.toNat + a1.toNat * 2^240 + a2.toNat * 2^480 + a3.toNat * 2^720 + a4.toNat * 2^960

theorem lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply word_ext; rw [word_toNat_lor, word_toNat_lor, Nat.or_comm]

theorem value_dig (a0 a1 a2 a3 a4 : UInt256) :
    CycleSubmission.ControlArithmetic.value (dig a0 a1 a2 a3 a4) = val5 a0 a1 a2 a3 a4 := by
  simp [CycleSubmission.ControlArithmetic.value, HistoricalSearch.MixedMontgomery.weighted,
    Finset.sum_range_succ, dig, val5]

theorem word0 (a0 a1 a2 a3 a4 : UInt256) :
    UInt256.lor a0 (UInt256.shiftLeft a1 (UInt256.ofNat 240)) =
      CycleSubmission.Packing.outputWord (dig a0 a1 a2 a3 a4) 0 := by
  rw [lor_comm]; rfl

theorem word1 (a0 a1 a2 a3 a4 : UInt256) :
    UInt256.lor (UInt256.shiftRight a1 (UInt256.ofNat 16)) (UInt256.shiftLeft a2 (UInt256.ofNat 224)) =
      CycleSubmission.Packing.outputWord (dig a0 a1 a2 a3 a4) 1 := by
  rw [lor_comm]; rfl

theorem word2 (a0 a1 a2 a3 a4 : UInt256) :
    UInt256.lor (UInt256.shiftRight a2 (UInt256.ofNat 32)) (UInt256.shiftLeft a3 (UInt256.ofNat 208)) =
      CycleSubmission.Packing.outputWord (dig a0 a1 a2 a3 a4) 2 := by
  rw [lor_comm]; rfl

theorem word3 (a0 a1 a2 a3 a4 : UInt256) :
    UInt256.lor (UInt256.shiftRight a3 (UInt256.ofNat 48)) (UInt256.shiftLeft a4 (UInt256.ofNat 192)) =
      CycleSubmission.Packing.outputWord (dig a0 a1 a2 a3 a4) 3 := by
  rw [lor_comm]; rfl

theorem done_represents (mem : ByteArray) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256)
    (h0 : a0.toNat < 2^240) (h1 : a1.toNat < 2^240) (h2 : a2.toNat < 2^240) (h3 : a3.toNat < 2^240)
    (h4 : a4.toNat < 2^240) (hv : val5 a0 a1 a2 a3 a4 < 2^1024) :
    Fast.Model.FastRepresents (done_mem mem a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp) 0 4
      (val5 a0 a1 a2 a3 a4) := by
  have hd : ∀ i < 9, (dig a0 a1 a2 a3 a4 i).toNat < 2^240 := by
    intro i hi
    interval_cases i <;> simp [dig] <;> assumption
  apply Fast.Model.fastRepresents_of_limbs (by simpa [Limbs.radix, ← Nat.pow_mul] using hv)
  intro k hk
  have hw := fun j hj => CycleSubmission.Packing.outputWord_toNat (dig a0 a1 a2 a3 a4) j hj hd
  rw [value_dig] at hw
  unfold done_mem
  rw [word0 a0 a1 a2 a3 a4, word1 a0 a1 a2 a3 a4, word2 a0 a1 a2 a3 a4, word3 a0 a1 a2 a3 a4]
  interval_cases k
  · simp (config := { decide := true }) only [read_past, read_same, Nat.zero_add]
    simpa [Limbs.radix] using hw 0 (by decide)
  · simp (config := { decide := true }) only [read_past, read_same, Nat.zero_add]
    simpa [Limbs.radix, ← Nat.pow_mul] using hw 1 (by decide)
  · simp (config := { decide := true }) only [read_past, read_same, Nat.zero_add]
    simpa [Limbs.radix, ← Nat.pow_mul] using hw 2 (by decide)
  · simp (config := { decide := true }) only [read_past, read_same, Nat.zero_add]
    simpa [Limbs.radix, ← Nat.pow_mul] using hw 3 (by decide)

theorem returned (s : State) (stk : List UInt256) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256)
    (h0 : a0.toNat < 2^240) (h1 : a1.toNat < 2^240) (h2 : a2.toNat < 2^240) (h3 : a3.toNat < 2^240)
    (h4 : a4.toNat < 2^240) (hv : val5 a0 a1 a2 a3 a4 < 2^1024) :
    (CycleSubmission.R5.Blocks.ctl5330_result
      {s with memory := done_mem s.memory a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp} stk).hReturn =
      Precompile.natToBytes (val5 a0 a1 a2 a3 a4) 128 :=
  Fast.Exp.readPadded_eq_natToBytes (ptr := 0) (count := 4) (msize := 128)
    (done_represents s.memory a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp h0 h1 h2 h3 h4 hv) (by decide)

end CycleSubmission.R5.TailMeaning
