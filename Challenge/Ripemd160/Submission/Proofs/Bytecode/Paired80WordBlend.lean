import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80WordBoolean
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Carry

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80WordBlend

open EvmSemantics PairedLaneUInt256Bridge Paired80WordBoolean

def wordBlend (x y : UInt256) : UInt256 :=
  UInt256.xor x (UInt256.land (UInt256.xor x y) upperWord)

theorem bits_wordBlend (x y : UInt256) :
    bits (wordBlend x y) = Paired80Carry.blend (bits x) (bits y) := by
  simp only [wordBlend, Paired80Carry.blend, bits_xor, bits_land, upperWord, bits_word]

#print axioms bits_wordBlend

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80WordBlend
