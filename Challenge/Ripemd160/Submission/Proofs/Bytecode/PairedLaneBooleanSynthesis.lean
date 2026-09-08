import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordBoolean

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBooleanSynthesis

open EvmSemantics
open PairedLaneBoolean PairedLaneUInt256Bridge PairedLaneWordBoolean

/-- Four-input identity with an arbitrary selector and arbitrary bit words. -/
theorem mixed_one (mask b c d m : BitVec w) :
    f 1 mask b c d ^^^ ((f 1 mask b c d ^^^ f 3 mask b c d) &&& m) =
      (b &&& c) ||| (d ^^^ ((b ^^^ m) &&& (c ||| d))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [f, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases b.getLsbD i <;> cases c.getLsbD i <;>
    cases d.getLsbD i <;> cases m.getLsbD i <;> rfl

#print axioms mixed_one

/-- The reverse lane choice also uses the same selector, without complement assumptions. -/
theorem mixed_three (mask b c d m : BitVec w) :
    f 3 mask b c d ^^^ ((f 3 mask b c d ^^^ f 1 mask b c d) &&& m) =
      c ^^^ ((d ^^^ (c &&& m)) &&& (b ^^^ (c ||| m))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [f, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases b.getLsbD i <;> cases c.getLsbD i <;>
    cases d.getLsbD i <;> cases m.getLsbD i <;> rfl

#print axioms mixed_three

def oneWord (b c d m : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land b c)
    (UInt256.xor d (UInt256.land (UInt256.xor b m) (UInt256.lor c d)))

def threeWord (b c d m : UInt256) : UInt256 :=
  UInt256.xor c
    (UInt256.land (UInt256.xor d (UInt256.land c m))
      (UInt256.xor b (UInt256.lor c m)))

theorem word_one (b c d m : UInt256) :
    UInt256.xor (wordF 1 b c d)
      (UInt256.land (UInt256.xor (wordF 1 b c d) (wordF 3 b c d)) m) =
      oneWord b c d m := by
  apply bits_injective
  simp only [oneWord, bits_xor, bits_land, bits_lor, bits_wordF]
  exact mixed_one _ _ _ _ _

#print axioms word_one

theorem word_three (b c d m : UInt256) :
    UInt256.xor (wordF 3 b c d)
      (UInt256.land (UInt256.xor (wordF 3 b c d) (wordF 1 b c d)) m) =
      threeWord b c d m := by
  apply bits_injective
  simp only [threeWord, bits_xor, bits_land, bits_lor, bits_wordF]
  exact mixed_three _ _ _ _ _

#print axioms word_three

theorem booleanPair_one (b c d : UInt256) :
    booleanPair 1 b c d = oneWord b c d upperWord := by
  exact word_one b c d upperWord

#print axioms booleanPair_one

theorem booleanPair_three (b c d : UInt256) :
    booleanPair 3 b c d = threeWord b c d upperWord := by
  exact word_three b c d upperWord

#print axioms booleanPair_three

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBooleanSynthesis
