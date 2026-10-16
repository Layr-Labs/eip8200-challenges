import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Accumulator
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! The direct 256-byte exit compares the final *whole* word, not the
27-byte segment projection.  The five low bytes are corrected before OR. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedAccumulator
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def correction : UInt256 := UInt256.ofNat 0x170d3b750f

def resultAcc256 (input : ByteArray) : UInt256 :=
  UInt256.lor
    (UInt256.xor
      (UInt256.xor (J2Accumulator.wordAt 7) (MachineState.readWord input 224)) correction)
    (J2Accumulator.accumulate input 256 7)

private theorem prefix_facts : ∀ k : Fin 7,
    J2Accumulator.offset k.val = 32*k.val ∧
    J2Accumulator.shift 256 k.val = 0 ∧
    J2Accumulator.wordAt k.val = RecognitionRecurrence.compareWord k.val := by decide

private theorem shr_zero (x : UInt256) : UInt256.shiftRight x 0 = x := by
  apply PairedLaneUInt256Bridge.bits_injective
  rw [show (0 : UInt256) = UInt256.ofNat 0 from rfl,
    PairedLaneUInt256Bridge.bits_shr x 0 (by decide)]
  simp

theorem prefix_eq (input : ByteArray) (k : Nat) (hk : k ≤ 7) :
    J2Accumulator.accumulate input 256 k = RecognitionAccumulator.fullAcc input k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨ho,hs,hw⟩ := prefix_facts ⟨k, by omega⟩
    rw [J2Accumulator.accumulate, RecognitionAccumulator.fullAcc, ih (by omega)]
    simp only [J2Accumulator.piece, ho, hs, hw, shr_zero]

theorem corrected_word :
    UInt256.xor (J2Accumulator.wordAt 7) correction = RecognitionRecurrence.compareWord 7 := by decide

theorem resultAcc256_eq (input : ByteArray) :
    resultAcc256 input = RecognitionAccumulator.resultAcc input 256 := by
  unfold resultAcc256
  rw [prefix_eq input 7 (by omega)]
  have hx (x : UInt256) :
      UInt256.xor (UInt256.xor (J2Accumulator.wordAt 7) x) correction =
        UInt256.xor x (RecognitionRecurrence.compareWord 7) := by
    rw [RawExpressionAC.xor_comm (J2Accumulator.wordAt 7) x,
      RawExpressionAC.xor_assoc, corrected_word]
  rw [hx]
  rfl

theorem resultAcc256_zero_iff (input : ByteArray) (hsize : input.size = 256) :
    resultAcc256 input = 0 ↔ input = RecognitionAccumulator.reference 256 := by
  rw [resultAcc256_eq]
  exact RecognitionAccumulator.resultAcc_zero_iff input 256 (by unfold RecognitionAccumulator.Allowed; omega) hsize

theorem resultAcc256_zero_iff_j2 (input : ByteArray) (hsize : input.size = 256) :
    resultAcc256 input = 0 ↔ J2Accumulator.resultAcc input 256 = 0 := by
  rw [resultAcc256_zero_iff input hsize, J2Accumulator.resultAcc_zero_iff input 256 (by unfold RecognitionAccumulator.Allowed; omega) hsize]

#print axioms resultAcc256_zero_iff
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedAccumulator
