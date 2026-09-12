import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Boolean

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80MaskedNot

open Paired80Core Paired80Boolean

/-- No input normalization is needed when the final mask is contained in p. -/
theorem masked_complement (x y p m : BitVec w) (h : p &&& m = m) :
    ((x ^^^ p) ||| y) &&& m = ((~~~x) ||| y) &&& m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbit : (p.getLsbD i && m.getLsbD i) = m.getLsbD i := by
    simpa only [BitVec.getLsbD_and] using congrArg (fun z => z.getLsbD i) h
  clear h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases hm : m.getLsbD i <;> cases hp : p.getLsbD i <;>
    cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all

theorem upper_masked_not (x y : BitVec 256) :
    ((x ^^^ pairMask) ||| y) &&& upperMask = ((~~~x) ||| y) &&& upperMask := by
  apply masked_complement
  simp only [pairMask, upperMask, pack_and, BitVec.and_zero, BitVec.and_allOnes]

theorem lower_masked_not (x y : BitVec 256) :
    ((x ^^^ pairMask) ||| y) &&& lowerMask = ((~~~x) ||| y) &&& lowerMask := by
  apply masked_complement
  simp only [pairMask, lowerMask, pack_and, BitVec.and_zero, BitVec.and_allOnes]

#print axioms masked_complement
#print axioms upper_masked_not
#print axioms lower_masked_not

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80MaskedNot
