import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordBoolean
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCarry

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordBlend

open EvmSemantics PairedLaneUInt256Bridge PairedLaneWordBoolean

def wordBlend (x y : UInt256) : UInt256 :=
  UInt256.xor x (UInt256.land (UInt256.xor x y) upperWord)

theorem bits_wordBlend (x y : UInt256) :
    bits (wordBlend x y) = PairedLaneCarry.blend (bits x) (bits y) := by
  simp only [wordBlend, PairedLaneCarry.blend, bits_xor, bits_land, upperWord, bits_word]

#print axioms bits_wordBlend

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordBlend
