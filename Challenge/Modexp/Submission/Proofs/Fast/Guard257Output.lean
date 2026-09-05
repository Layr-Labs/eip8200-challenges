import Challenge.Modexp.Submission.Proofs.Fast.Guard257State
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Output

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.Guard257State
open Challenge.EvmProof.Memory

def answer : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639935

theorem pointwise_read (i : Nat) (hi : i < 33) :
    (MachineState.readPadded answerMemory 0 33)[i]?.getD 0 =
      (Precompile.natToBytes answer 33)[i]?.getD 0 := by
  rw [readPadded_getElem?_getD, if_pos hi]
  have hpre : (Precompile.natToBytes answer 33)[i]?.getD 0 =
      UInt8.ofNat (answer / 256 ^ (33 - 1 - i) % 256) :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 33 _ hi
  rw [hpre]
  dsimp [answerMemory, storeWord]
  rw [MachineState.writeBytes_getElem?_getD]
  simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [MachineState.writeBytes_getElem?_getD]
  simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have hzword (k : Nat) (hk : k < 32) :
      (Data.Bytes.natToBytesPadded (UInt256.toNat 0) 32)[k]?.getD 0 =
        UInt8.ofNat ((UInt256.toNat 0) / 256 ^ (32 - 1 - k) % 256) :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 32 k hk
  have hword (k : Nat) (hk : k < 32) :
      (Data.Bytes.natToBytesPadded (UInt256.toNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) 32)[k]?.getD 0 =
        UInt8.ofNat ((UInt256.toNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) / 256 ^ (32 - 1 - k) % 256) :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 32 k hk
  interval_cases i
  · rw [hzword 0 (by decide)]; decide
  · rw [hword 0 (by decide)]; decide
  · rw [hword 1 (by decide)]; decide
  · rw [hword 2 (by decide)]; decide
  · rw [hword 3 (by decide)]; decide
  · rw [hword 4 (by decide)]; decide
  · rw [hword 5 (by decide)]; decide
  · rw [hword 6 (by decide)]; decide
  · rw [hword 7 (by decide)]; decide
  · rw [hword 8 (by decide)]; decide
  · rw [hword 9 (by decide)]; decide
  · rw [hword 10 (by decide)]; decide
  · rw [hword 11 (by decide)]; decide
  · rw [hword 12 (by decide)]; decide
  · rw [hword 13 (by decide)]; decide
  · rw [hword 14 (by decide)]; decide
  · rw [hword 15 (by decide)]; decide
  · rw [hword 16 (by decide)]; decide
  · rw [hword 17 (by decide)]; decide
  · rw [hword 18 (by decide)]; decide
  · rw [hword 19 (by decide)]; decide
  · rw [hword 20 (by decide)]; decide
  · rw [hword 21 (by decide)]; decide
  · rw [hword 22 (by decide)]; decide
  · rw [hword 23 (by decide)]; decide
  · rw [hword 24 (by decide)]; decide
  · rw [hword 25 (by decide)]; decide
  · rw [hword 26 (by decide)]; decide
  · rw [hword 27 (by decide)]; decide
  · rw [hword 28 (by decide)]; decide
  · rw [hword 29 (by decide)]; decide
  · rw [hword 30 (by decide)]; decide
  · rw [hword 31 (by decide)]; decide

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 33 =
      Precompile.natToBytes answer 33 := by
  apply ByteArray.ext_getElem
  · rw [readPadded_size, Precompile.natToBytes, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hia hib
    rw [← getD0_eq_getElem _ _ hia, ← getD0_eq_getElem _ _ hib]
    have hi : i < 33 := by simpa using hia
    exact pointwise_read i hi

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Output
