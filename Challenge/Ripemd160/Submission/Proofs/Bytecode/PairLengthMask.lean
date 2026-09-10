import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge
import Challenge.EvmProof.Word
import Mathlib.Data.Nat.Bitwise

set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairLengthMask
open EvmSemantics
open PairedLaneUInt256Bridge

private theorem split64 (x : UInt256) :
    UInt256.lor (UInt256.land (UInt256.lnot 64) x) (UInt256.land 64 x) = x := by
  apply bits_injective
  simp only [bits_lor, bits_land, bits_lnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    hi, decide_true, Bool.true_and]
  cases (bits (64 : UInt256)).getLsbD i <;>
    cases (bits x).getLsbD i <;> rfl

private theorem and64_cases (x : UInt256) :
    UInt256.land 64 x = 0 ∨ UInt256.land 64 x = 64 := by
  have h := Nat.two_pow_and x.toNat 6
  norm_num at h
  cases hb : x.toNat.testBit 6 with
  | false =>
    left
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_land]
    change 64 &&& x.toNat = 0
    simpa [hb] using h
  | true =>
    right
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_land]
    change 64 &&& x.toNat = 64
    simpa [hb] using h

theorem clear64_eq56 (x : UInt256) :
    UInt256.land (UInt256.lnot 64) x = 56 ↔ x = 56 ∨ x = 120 := by
  constructor
  · intro h
    have hs := split64 x
    rcases and64_cases x with ha | ha
    · left
      rw [h, ha] at hs
      have hc : UInt256.lor (56 : UInt256) 0 = 56 := by decide
      rw [hc] at hs
      exact hs.symm
    · right
      rw [h, ha] at hs
      have hc : UInt256.lor (56 : UInt256) 64 = 120 := by decide
      rw [hc] at hs
      exact hs.symm
  · rintro (rfl | rfl) <;> decide

private theorem eq_as_if (a b : UInt256) :
    UInt256.eq a b = if a = b then (1 : UInt256) else 0 := by
  have he : a.toNat = b.toNat ↔ a = b :=
    ⟨fun h => Challenge.EvmProof.Word.word_ext h,
      fun h => congrArg UInt256.toNat h⟩
  simp only [UInt256.eq, he]

theorem flags (x : UInt256) :
    UInt256.eq 56 (UInt256.land (UInt256.lnot 64) x) =
      UInt256.lor (UInt256.eq 120 x) (UInt256.eq 56 x) := by
  by_cases h56 : x = 56
  · subst x; decide
  by_cases h120 : x = 120
  · subst x; decide
  have hm : UInt256.land (UInt256.lnot 64) x ≠ 56 := by
    intro h
    rcases (clear64_eq56 x).mp h with h | h
    · exact h56 h
    · exact h120 h
  rw [eq_as_if, eq_as_if, eq_as_if,
    if_neg (Ne.symm hm), if_neg (Ne.symm h120), if_neg (Ne.symm h56)]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairLengthMask
