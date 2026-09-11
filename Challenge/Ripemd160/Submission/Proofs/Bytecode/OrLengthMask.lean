import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairLengthMask

set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.OrLengthMask
open EvmSemantics
open PairedLaneUInt256Bridge

private theorem clear_set64 (x : UInt256) :
    UInt256.land (UInt256.lnot 64) (UInt256.lor 64 x) =
      UInt256.land (UInt256.lnot 64) x := by
  apply bits_injective
  simp only [bits_lor, bits_land, bits_lnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    hi, decide_true, Bool.true_and]
  cases (bits (64 : UInt256)).getLsbD i <;>
    cases (bits x).getLsbD i <;> rfl

theorem set64_eq120 (x : UInt256) :
    UInt256.lor 64 x = 120 ↔ x = 56 ∨ x = 120 := by
  constructor
  · intro h
    apply (PairLengthMask.clear64_eq56 x).mp
    have hc := congrArg (UInt256.land (UInt256.lnot 64)) h
    rw [clear_set64] at hc
    have hk : UInt256.land (UInt256.lnot 64) (120 : UInt256) = 56 := by decide
    exact hc.trans hk
  · rintro (rfl | rfl) <;> decide

private theorem eq_as_if (a b : UInt256) :
    UInt256.eq a b = if a = b then (1 : UInt256) else 0 := by
  have he : a.toNat = b.toNat ↔ a = b :=
    ⟨fun h => Challenge.EvmProof.Word.word_ext h,
      fun h => congrArg UInt256.toNat h⟩
  by_cases hab : a = b
  · simp only [UInt256.eq, he, hab, ite_true]
    decide
  · simp only [UInt256.eq, he, hab, ite_false]
    decide

theorem flags (x : UInt256) :
    UInt256.eq 120 (UInt256.lor 64 x) =
      UInt256.lor (UInt256.eq 120 x) (UInt256.eq 56 x) := by
  by_cases h56 : x = 56
  · subst x; decide
  by_cases h120 : x = 120
  · subst x; decide
  have hm : UInt256.lor 64 x ≠ 120 := by
    intro h
    rcases (set64_eq120 x).mp h with h | h
    · exact h56 h
    · exact h120 h
  rw [eq_as_if, eq_as_if, eq_as_if,
    if_neg (Ne.symm hm), if_neg (Ne.symm h120), if_neg (Ne.symm h56)]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.OrLengthMask
