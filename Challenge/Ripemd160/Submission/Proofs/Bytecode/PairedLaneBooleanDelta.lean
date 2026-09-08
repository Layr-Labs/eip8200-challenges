import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordBoolean

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBooleanDelta

open EvmSemantics
open PairedLaneBoolean PairedLaneUInt256Bridge PairedLaneWordBoolean

/-- This identity holds for arbitrary bits, not only normalized packed cells. -/
theorem f13_delta (mask b c d : BitVec w) :
    f 1 mask b c d ^^^ f 3 mask b c d =
      d ^^^ (c &&& ~~~(b ^^^ d)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [f, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases b.getLsbD i <;> cases c.getLsbD i <;> cases d.getLsbD i <;> rfl

def deltaWord (b c d : UInt256) : UInt256 :=
  UInt256.xor d (UInt256.land c (UInt256.lnot (UInt256.xor b d)))

theorem word_f13_delta (b c d : UInt256) :
    UInt256.xor (wordF 1 b c d) (wordF 3 b c d) = deltaWord b c d := by
  apply bits_injective
  simp only [deltaWord, bits_xor, bits_land, bits_lnot, bits_wordF]
  exact f13_delta _ _ _ _

theorem booleanPair_one_delta (b c d : UInt256) :
    booleanPair 1 b c d =
      UInt256.xor (wordF 1 b c d) (UInt256.land (deltaWord b c d) upperWord) := by
  change UInt256.xor (wordF 1 b c d)
    (UInt256.land (UInt256.xor (wordF 1 b c d) (wordF 3 b c d)) upperWord) = _
  rw [word_f13_delta]

theorem booleanPair_three_delta (b c d : UInt256) :
    booleanPair 3 b c d =
      UInt256.xor (wordF 3 b c d) (UInt256.land (deltaWord b c d) upperWord) := by
  have h : UInt256.xor (wordF 3 b c d) (wordF 1 b c d) = deltaWord b c d := by
    apply bits_injective
    rw [bits_xor]
    have h0 := congrArg bits (word_f13_delta b c d)
    rw [bits_xor] at h0
    exact (BitVec.xor_comm _ _).trans h0
  change UInt256.xor (wordF 3 b c d)
    (UInt256.land (UInt256.xor (wordF 3 b c d) (wordF 1 b c d)) upperWord) = _
  rw [h]

#print axioms f13_delta
#print axioms word_f13_delta
#print axioms booleanPair_one_delta
#print axioms booleanPair_three_delta

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBooleanDelta
