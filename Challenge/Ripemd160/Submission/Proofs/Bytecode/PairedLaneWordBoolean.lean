import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneMaskedNot

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordBoolean

open EvmSemantics
open PairedLaneCore PairedLaneBoolean PairedLaneUInt256Bridge PairedLaneMaskedNot

def pairWord : UInt256 := word pairMask
def upperWord : UInt256 := word upperMask
def lowerWord : UInt256 := word lowerMask

def wordF (j : Nat) (b c d : UInt256) : UInt256 :=
  match j with
  | 0 => UInt256.xor (UInt256.xor b c) d
  | 1 => UInt256.xor (UInt256.land (UInt256.xor c d) b) d
  | 2 => UInt256.xor (UInt256.lor (UInt256.xor c pairWord) b) d
  | 3 => UInt256.xor (UInt256.land (UInt256.xor b c) d) c
  | _ => UInt256.xor (UInt256.lor (UInt256.xor d pairWord) c) b

theorem bits_wordF (j : Nat) (b c d : UInt256) :
    bits (wordF j b c d) = f j pairMask (bits b) (bits c) (bits d) := by
  cases j with
  | zero => simp only [wordF, f, bits_xor]
  | succ j => cases j with
    | zero => simp only [wordF, f, bits_xor, bits_land]
    | succ j => cases j with
      | zero => simp only [wordF, f, bits_xor, bits_lor, pairWord, bits_word]
      | succ j => cases j with
        | zero => simp only [wordF, f, bits_xor, bits_land]
        | succ j => simp only [wordF, f, bits_xor, bits_lor, pairWord, bits_word]

#print axioms bits_wordF

def booleanPair (j : Nat) (b c d : UInt256) : UInt256 :=
  match j with
  | 0 => UInt256.xor (wordF 0 b c d)
      (UInt256.land (UInt256.lor (UInt256.lnot c) d) upperWord)
  | 1 => UInt256.xor (wordF 1 b c d)
      (UInt256.land (UInt256.xor (wordF 1 b c d) (wordF 3 b c d)) upperWord)
  | 2 => wordF 2 b c d
  | 3 => UInt256.xor (wordF 3 b c d)
      (UInt256.land (UInt256.xor (wordF 3 b c d) (wordF 1 b c d)) upperWord)
  | _ => UInt256.xor (wordF 0 b c d)
      (UInt256.land (UInt256.lor (UInt256.lnot c) d) lowerWord)

theorem bits_booleanPair (j : Nat) (b c d : UInt256) :
    bits (booleanPair j b c d) = pairedF j (bits b) (bits c) (bits d) := by
  cases j with
  | zero =>
    simp only [booleanPair, pairedF, bits_xor, bits_land, bits_lor, bits_lnot,
      upperWord, bits_word, bits_wordF, upper_masked_not]
  | succ j => cases j with
    | zero =>
      simp only [booleanPair, pairedF, bits_xor, bits_land, upperWord, bits_word, bits_wordF]
    | succ j => cases j with
      | zero => exact bits_wordF 2 b c d
      | succ j => cases j with
        | zero =>
          simp only [booleanPair, pairedF, bits_xor, bits_land, upperWord, bits_word, bits_wordF]
        | succ j =>
          simp only [booleanPair, pairedF, bits_xor, bits_land, bits_lor, bits_lnot,
            lowerWord, bits_word, bits_wordF, lower_masked_not]

#print axioms bits_booleanPair

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordBoolean
