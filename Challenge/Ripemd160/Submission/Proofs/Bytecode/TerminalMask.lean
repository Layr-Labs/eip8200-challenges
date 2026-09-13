import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalMask
open EvmSemantics
open PairedStartupTrace PairedTailTrace PairedLaneUInt256Bridge

private theorem mask32_pair (x : UInt256) :
    Challenge.EvmProof.Word.mask32 (UInt256.land pairWord x) =
      Challenge.EvmProof.Word.mask32 x := by
  apply bits_injective
  change bits (UInt256.land (UInt256.land pairWord x) lowerWord) =
    bits (UInt256.land x lowerWord)
  simp only [bits_land]
  rw [BitVec.and_comm (bits pairWord) (bits x), BitVec.and_assoc]
  have h : bits pairWord &&& bits lowerWord = bits lowerWord := by decide
  rw [h]

private theorem mask32_pair_shr (x : UInt256) :
    Challenge.EvmProof.Word.mask32
      (UInt256.shiftRight (UInt256.land pairWord x) (UInt256.ofNat 128)) =
    Challenge.EvmProof.Word.mask32
      (UInt256.shiftRight x (UInt256.ofNat 128)) := by
  apply bits_injective
  change bits (UInt256.land
      (UInt256.shiftRight (UInt256.land pairWord x) (UInt256.ofNat 128)) lowerWord) =
    bits (UInt256.land (UInt256.shiftRight x (UInt256.ofNat 128)) lowerWord)
  simp only [bits_land, bits_shr _ 128 (by decide), BitVec.ushiftRight_and_distrib]
  rw [BitVec.and_comm (bits pairWord >>> 128) (bits x >>> 128), BitVec.and_assoc]
  have h : (bits pairWord >>> 128) &&& bits lowerWord = bits lowerWord := by decide
  rw [h]

theorem toUInt32_pair (x : UInt256) :
    Challenge.EvmProof.Word.toUInt32 (UInt256.land pairWord x) =
      Challenge.EvmProof.Word.toUInt32 x := by
  have h := congrArg Challenge.EvmProof.Word.toUInt32 (mask32_pair x)
  simpa only [Challenge.EvmProof.Word.mask32_eq_ofUInt32,
    Challenge.EvmProof.Word.toUInt32_ofUInt32] using h

theorem toUInt32_pair_shr (x : UInt256) :
    Challenge.EvmProof.Word.toUInt32
      (UInt256.shiftRight (UInt256.land pairWord x) (UInt256.ofNat 128)) =
    Challenge.EvmProof.Word.toUInt32
      (UInt256.shiftRight x (UInt256.ofNat 128)) := by
  have h := congrArg Challenge.EvmProof.Word.toUInt32 (mask32_pair_shr x)
  simpa only [Challenge.EvmProof.Word.mask32_eq_ofUInt32,
    Challenge.EvmProof.Word.toUInt32_ofUInt32] using h

theorem combine_mask_pair (memory : ByteArray) (address : Nat) (left right : UInt256) :
    combine memory address lowerWord (UInt256.land pairWord left) (UInt256.land pairWord right) =
      combine memory address lowerWord left right := by
  simp only [tail_combine_normalized, toUInt32_pair, toUInt32_pair_shr]

theorem resultMemory_mask_bd (memory : ByteArray) (q : PairedTailTrace.Frame)
    (hlower : q.lower = lowerWord) :
    resultMemory memory {q with b := UInt256.land pairWord q.b, d := UInt256.land pairWord q.d} = resultMemory memory q := by
  simp only [resultMemory, result0, result1, result2, result3, result4, hlower,
    tail_combine_normalized, toUInt32_pair, toUInt32_pair_shr]

#print axioms combine_mask_pair
#print axioms resultMemory_mask_bd
end Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalMask
