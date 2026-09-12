import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144MaskedNot

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordBooleanBridge

open EvmSemantics
open Paired144Core Paired144Boolean PairedLaneUInt256Bridge Paired144MaskedNot

open Paired144WordRound

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

theorem bits_booleanPair (j : Nat) (b c d : UInt256) :
    bits (booleanPair j b c d) = pairedF j (bits b) (bits c) (bits d) := by
  cases j with
  | zero =>
    simp only [booleanPair, pairedF, bits_xor, bits_land, bits_lor, bits_lnot,
      upperWord, bits_word, bits_wordF]
    exact congrArg (fun z => f 0 pairMask (bits b) (bits c) (bits d) ^^^ z) (upper_masked_not (bits c) (bits d)).symm
  | succ j => cases j with
    | zero =>
      simp only [booleanPair, pairedF, bits_xor, bits_land, upperWord, upperMask, bits_word, bits_wordF]
    | succ j => cases j with
      | zero => exact bits_wordF 2 b c d
      | succ j => cases j with
        | zero =>
          simp only [booleanPair, pairedF, bits_xor, bits_land, upperWord, upperMask, bits_word, bits_wordF]
        | succ j =>
          simp only [booleanPair, pairedF, bits_xor, bits_land, bits_lor, bits_lnot,
            lowerWord, bits_word, bits_wordF]
          exact congrArg (fun z => f 0 pairMask (bits b) (bits c) (bits d) ^^^ z) (lower_masked_not (bits c) (bits d)).symm

#print axioms bits_booleanPair

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordBooleanBridge
