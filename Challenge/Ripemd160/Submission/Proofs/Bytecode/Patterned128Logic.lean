import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Data
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanMask
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Logic

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedInputData PatternedSwar
open PatternedWordData
open Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjection
open Challenge.Ripemd160.Submission.Proofs.Bytecode.TailProjectionInstances

theorem rawShift_128 (k : Nat) (hk : k < 4) :
    rawShift 128 (UInt256.ofNat (32 * k)) = wordShift 128 k := by
  interval_cases k <;> decide

theorem guardWord_projection_128 (j : Nat) (hj : j < 4) :
    UInt256.shiftRight (guardWord j) (wordShift 128 j) =
      UInt256.shiftRight (MachineState.readWord Patterned128Data.data (32 * j))
        (wordShift 128 j) := by
  have hg : guardWord j = expectedWordAt j := by
    interval_cases j <;> simp
  rw [hg, Patterned128Data.readWord_data j hj]

theorem scanAcc_eq_guardedAcc_128 (input : ByteArray) (hsize : input.size = 128)
    (n : Nat) (hn : n ≤ 4) :
    scanAcc input n = guardedAcc input guardWord (wordShift 128) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scanAcc, guardedAcc, ih (by omega)]
    rw [maskShift, hsize, rawShift_128 n (by omega)]
    exact lor_comm _ _

theorem scanAcc_zero_iff_eq (input : ByteArray) (hsize : input.size = 128) :
    scanAcc input 4 = 0 ↔ input = Patterned128Data.data := by
  rw [scanAcc_eq_guardedAcc_128 input hsize 4 (by omega)]
  change guardedAcc input guardWord
      (fun j => UInt256.ofNat ((32 - min 32 (128 - 32 * j)) * 8)) 4 = 0 ↔
      input = Patterned128Data.data
  have hs : input.size = Patterned128Data.data.size := by
    simpa only [Patterned128Data.data_size] using hsize
  have hc : Patterned128Data.data.size ≤ 32 * 4 := by
    rw [Patterned128Data.data_size]
  simpa only [Patterned128Data.data_size, wordShift] using
    (guardedAcc_zero_iff_eq input Patterned128Data.data guardWord 4 hs hc
      (by simpa only [Patterned128Data.data_size, wordShift] using guardWord_projection_128))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Logic

#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Logic.rawShift_128
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Logic.guardWord_projection_128
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Logic.scanAcc_eq_guardedAcc_128
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Logic.scanAcc_zero_iff_eq
