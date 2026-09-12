import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Core
import Init.Data.BitVec.Bitblast

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Product

open Paired80Core

def factor : BitVec 256 := BitVec.ofNat 256 4294967297

theorem mask_shift_disjoint :
    (pairMask <<< 32) &&& pairMask = 0#256 := by
  decide

private theorem and_exchange (a b c d : BitVec w) :
    (a &&& b) &&& (c &&& d) = (a &&& c) &&& (b &&& d) := by
  rw [BitVec.and_assoc a b (c &&& d),
    ← BitVec.and_assoc b c d, BitVec.and_comm b c,
    BitVec.and_assoc c b d, ← BitVec.and_assoc a c (b &&& d)]

theorem normalized_shift_disjoint (x : BitVec 256) :
    (normalize x <<< 32) &&& normalize x = 0#256 := by
  simp only [normalize_eq_and, BitVec.shiftLeft_and_distrib]
  calc
    ((x <<< 32) &&& (pairMask <<< 32)) &&& (x &&& pairMask) =
        ((x <<< 32) &&& x) &&& ((pairMask <<< 32) &&& pairMask) := by
      exact and_exchange _ _ _ _
    _ = 0#256 := by
      rw [mask_shift_disjoint]
      exact BitVec.and_zero

theorem factor_copies_normalized (x : BitVec 256) :
    normalize x * factor = (normalize x <<< 32) ||| normalize x := by
  rw [show factor = BitVec.twoPow 256 32 + 1#256 by decide,
    BitVec.mul_add, BitVec.mul_twoPow_eq_shiftLeft, BitVec.mul_one]
  exact BitVec.add_eq_or_of_and_eq_zero _ _ (normalized_shift_disjoint x)

#print axioms mask_shift_disjoint
#print axioms normalized_shift_disjoint
#print axioms factor_copies_normalized

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Product
