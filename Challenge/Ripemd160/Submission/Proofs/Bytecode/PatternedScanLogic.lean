import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedInputData PatternedSwar

open PatternedWordData TailProjection TailProjectionInstances

theorem guardWord_eq (j : Nat) (hj : j < 31) : guardWord j = expectedWordAt j := by
  interval_cases j <;> simp

theorem scanAcc_eq_guardedAcc_376 (input : ByteArray) (hsize : input.size = 376)
    (n : Nat) (hn : n ≤ 12) :
    scanAcc input n = guardedAcc input guardWord (wordShift 376) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scanAcc, guardedAcc, ih (by omega)]
    rw [maskShift, hsize, rawShift_376 n (by omega)]
    exact lor_comm _ _

theorem scanAcc_eq_guardedAcc_1000 (input : ByteArray) (hsize : input.size = 1000)
    (n : Nat) (hn : n ≤ 32) :
    scanAcc input n = guardedAcc input guardWord (wordShift 1000) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [scanAcc, guardedAcc, ih (by omega)]
    rw [maskShift, hsize, rawShift_1000 n (by omega)]
    exact lor_comm _ _

theorem scanAccFinal_zero_iff_eq (input : ByteArray) (hsize : input.size = 1000) :
    scanAccFinal input = 0 ↔ input = patternedInput := by
  rw [scanAccFinal, scanAcc_eq_guardedAcc_1000 input hsize 32 (by omega)]
  exact acc1000_zero_iff input hsize

theorem scanAccFinal_patterned : scanAccFinal patternedInput = 0 :=
  (scanAccFinal_zero_iff_eq patternedInput patternedInput_size).2 rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
