import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordBoolean

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBooleanFactoring

open EvmSemantics
open PairedLaneUInt256Bridge PairedLaneWordBoolean

/-- Factoring holds for arbitrary bit words and an arbitrary selector. -/
theorem factored_bits (b c d m : BitVec w) :
    ((b ^^^ c) ^^^ d) ^^^ (((~~~c) ||| d) &&& m) =
      b ^^^ (c ^^^ (m ^^^ (d ||| (m &&& c)))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases b.getLsbD i <;> cases c.getLsbD i <;>
    cases d.getLsbD i <;> cases m.getLsbD i <;> rfl

#print axioms factored_bits

def factoredWord (b c d m : UInt256) : UInt256 :=
  UInt256.xor b (UInt256.xor c (UInt256.xor m
    (UInt256.lor d (UInt256.land m c))))

theorem factored_word (b c d m : UInt256) :
    UInt256.xor (UInt256.xor (UInt256.xor b c) d)
      (UInt256.land (UInt256.lor (UInt256.lnot c) d) m) =
      factoredWord b c d m := by
  apply bits_injective
  simp only [factoredWord, bits_xor, bits_land, bits_lor, bits_lnot]
  exact factored_bits _ _ _ _

#print axioms factored_word

theorem booleanPair_zero (b c d : UInt256) :
    booleanPair 0 b c d = factoredWord b c d upperWord := by
  exact factored_word b c d upperWord

#print axioms booleanPair_zero

theorem booleanPair_four (b c d : UInt256) :
    booleanPair 4 b c d = factoredWord b c d lowerWord := by
  exact factored_word b c d lowerWord

#print axioms booleanPair_four

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBooleanFactoring

