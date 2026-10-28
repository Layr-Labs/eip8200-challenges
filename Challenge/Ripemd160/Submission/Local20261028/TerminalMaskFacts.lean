import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolByte
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableMemory
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdTerminalMasks20261027
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode

def mask (w : UInt256) : UInt256 := UInt256.land w (UInt256.ofNat 4294967295)

theorem low_byte (w : UInt256) (i : Nat) (hl : 28 ≤ i) (hi : i < 32) :
    (Data.Bytes.natToBytesPadded (mask w).toNat 32)[i]?.getD 0 =
      (Data.Bytes.natToBytesPadded w.toNat 32)[i]?.getD 0 := by
  rw [PoolByte.encoded _ _ hi, PoolByte.encoded _ _ hi]
  unfold mask
  rw [PoolByte.land]
  have hm : PoolByte.byte (UInt256.ofNat 4294967295) i = 255 := by
    interval_cases i <;> decide
  rw [hm, PoolByte.and255]

def stores (m : ByteArray) (a b c d e : UInt256) : ByteArray :=
  PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord
    (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord
    (PairedScheduleMemory.writeWord m 16 a) 12 b) 8 c) 4 d) 0 e

theorem stores_getD (m : ByteArray) (a b c d e : UInt256) (i : Nat) :
    (stores m (mask a) (mask b) (mask c) (mask d) e)[i]?.getD 0 =
      (stores m a b c d e)[i]?.getD 0 := by
  simp only [stores, PairedScheduleMemory.writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  split_ifs <;> first | rfl | exact low_byte _ _ (by omega) (by omega)

theorem stores_read (m : ByteArray) (a b c d e : UInt256) (offset : Nat) :
    MachineState.readWord (stores m (mask a) (mask b) (mask c) (mask d) e) offset =
      MachineState.readWord (stores m a b c d e) offset := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro i hi
  exact stores_getD m a b c d e (offset+i)

theorem stores_eq (m : ByteArray) (a b c d e : UInt256) :
    stores m (mask a) (mask b) (mask c) (mask d) e = stores m a b c d e := by
  apply ByteArray.ext_getElem
  · simp only [stores, PairedScheduleMemory.writeWord_size]
  · intro i hleft hright
    rw [← Memory.getD0_eq_getElem _ _ hleft, ← Memory.getD0_eq_getElem _ _ hright]
    exact stores_getD m a b c d e i

#print axioms low_byte
#print axioms stores_getD
#print axioms stores_read
#print axioms stores_eq
end RipemdTerminalMasks20261027
