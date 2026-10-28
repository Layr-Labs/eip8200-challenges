import Challenge.Ripemd160.Submission.Local20261028.CoreEndianBase
import Challenge.Ripemd160.Submission.Local20261028.FirstMessageReady
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstInitial
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedLaneUInt256Bridge PairedScheduleMemory RipemdMemoryBridge20261028
def highWord : UInt256 := UInt256.ofNat (2^231+2^40)
def memory (m : ByteArray) : ByteArray :=
  writeWord (writeWord m 162 highWord) 252 (PairedScheduleData.reversedWord (MachineState.readWord m 1056))
theorem reversed_byte (w : UInt256) (i : Nat) (hi : i < 32) :
    PoolByte.byte (PairedScheduleData.reversedWord w) i = PoolByte.byte w (4*(i/4)+3-i%4) := by
  rw [PairedScheduleData.reversedWord_eq_packed]
  apply UInt8.eq_of_toBitVec_eq
  simp only [PoolByte.byte, UInt8.toBitVec_ofBitVec, DenseScheduleMemory.DensePacked.packed,
    DenseScheduleMemory.DensePacked.shr, DenseScheduleMemory.DensePacked.shl,
    bits_land, bits_lor, bits_shr _ 8 (by decide), bits_shr _ 16 (by decide),
    bits_shl _ 8 (by decide), bits_shl _ 16 (by decide),
    DenseScheduleMemory.DensePacked.mask8, DenseScheduleMemory.DensePacked.mask16, bits_ofNat]
  interval_cases i <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;> interval_cases j <;>
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
theorem outside (m : ByteArray) (a : Nat) (ha : 284 ≤ a) :
    (memory m)[a]?.getD 0 = m[a]?.getD 0 := by
  simp only [memory, write_getD, if_neg (by omega : ¬ (252 ≤ a ∧ a < 252+32)),
    if_neg (by omega : ¬ (162 ≤ a ∧ a < 162+32))]
theorem high_bytes (m : ByteArray) (i : Nat) (hi : i < 32) :
    PoolByte.byte highWord i = FirstMemory.value m FirstMemory.fixedHigh[i]! := by
  interval_cases i <;> rfl
theorem matches_initial (m : ByteArray) (hz : ∀ a, a < 1056 → m[a]?.getD 0 = 0) :
    Matches (memory m) FirstMemory.initial (FirstMemory.value (memory m)) := by
  intro a
  by_cases hh : 162 ≤ a ∧ a < 194
  · rw [memory, write_getD, if_neg (by omega), write_getD, if_pos (by omega)]
    rw [FirstMemory.initial, if_pos hh]
    exact high_bytes _ _ (by omega)
  by_cases hl : 252 ≤ a ∧ a < 284
  · have hi : a-252 < 32 := by omega
    have hsym : 1 ≤ 1+((a-252)/4)*4+3-(a-252)%4 ∧
        1+((a-252)/4)*4+3-(a-252)%4 ≤ 32 := by omega
    rw [memory, write_getD, if_pos (by omega), reversed_byte _ _ hi, PoolByte.read _ _ _ (by omega)]
    rw [FirstMemory.initial, if_neg hh, if_pos hl]
    simp only [FirstMemory.value, if_neg (by omega : ¬ 1+((a-252)/4)*4+3-(a-252)%4 = 0),
      if_neg (by omega : ¬ 1+((a-252)/4)*4+3-(a-252)%4 = 33),
      if_neg (by omega : ¬ 1+((a-252)/4)*4+3-(a-252)%4 = 34), if_pos hsym.2]
    change m[1056 + (4*((a-252)/4)+3-(a-252)%4)]?.getD 0 =
      (memory m)[1056 + (1+(a-252)/4*4+3-(a-252)%4)-1]?.getD 0
    rw [outside _ _ (by omega)]
    congr 2
    omega
  by_cases hd : 1056 ≤ a ∧ a < 1088
  · have hsym : 1 ≤ 1+a-1056 ∧ 1+a-1056 ≤ 32 := by omega
    rw [FirstMemory.initial, if_neg hh, if_neg hl, if_pos hd]
    simp only [FirstMemory.value, if_neg (by omega : ¬ 1+a-1056 = 0),
      if_neg (by omega : ¬ 1+a-1056 = 33), if_neg (by omega : ¬ 1+a-1056 = 34), if_pos hsym.2]
    congr 2
    omega
  by_cases ha : a < 1088
  · rw [FirstMemory.initial, if_neg hh, if_neg hl, if_neg hd, if_pos ha]
    change (memory m)[a]?.getD 0 = 0
    simp only [memory, write_getD, if_neg (by omega : ¬ (252 ≤ a ∧ a < 252+32)),
      if_neg (by omega : ¬ (162 ≤ a ∧ a < 162+32))]
    exact hz a (by omega)
  · rw [FirstMemory.initial, if_neg hh, if_neg hl, if_neg hd, if_neg ha]
    simp only [FirstMemory.value, if_neg (by omega : ¬ 1000+a = 0),
      if_neg (by omega : ¬ 1000+a = 33), if_neg (by omega : ¬ 1000+a = 34),
      if_neg (by omega : ¬ 1000+a ≤ 32), if_pos (by omega : 1000 ≤ 1000+a)]
    congr 2
    omega
#print axioms reversed_byte
#print axioms matches_initial
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstInitial
