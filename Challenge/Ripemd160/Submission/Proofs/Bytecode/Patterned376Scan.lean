import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanLoopMore
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanLoopLast
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanExitHit
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanExitMiss
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanReturn
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open Patterned376InputData Patterned376Digest Patterned376GuardSpec Patterned376ScanLogic

private def gasSteps_loop (input : ByteArray) (hsize : input.size = 376) :
    GasSteps (loopState input 0) (loopExitState input) := by
  let step : ∀ n, n < 375 → GasSteps (loopState input n) (loopState input (n + 1)) :=
    fun n hn => sound loopPath (run_loop_more input n hn (by rw [hsize]; omega))
  exact (GasSteps.iterateBounded 375 step).trans
    (sound loopPath (run_loop_last input (by rw [hsize]; decide)))

def gasSteps_fromEntry_hit (input : ByteArray) (hsize : input.size = 376)
    (hz : scanAcc input 376 = 0) :
    GasSteps (patterned376Entry input) (returnedState input) :=
  (gasSteps_loop input hsize).trans
    ((sound exitPath (run_exit_hit input hz)).trans
      (by
        have h := scanAcc_zero_iff_eq input hsize |>.1 hz
        subst input
        exact sound returnPath run_return))

def gasSteps_fromEntry_miss (input : ByteArray) (hsize : input.size = 376)
    (hne : scanAcc input 376 ≠ 0) :
    GasSteps (patterned376Entry input) (fallbackState input) :=
  (gasSteps_loop input hsize).trans
    (sound exitPath (run_exit_miss input hne))

def gasSteps_patterned376 :
    GasSteps (patterned376Entry patterned376Input) (returnedState patterned376Input) :=
  gasSteps_fromEntry_hit patterned376Input patterned376Input_size
    (scanAcc_patterned376 376 (by decide))

def gasSteps_patterned376_miss (input : ByteArray) (hsize : input.size = 376)
    (hne : input ≠ patterned376Input) :
    GasSteps (patterned376Entry input) (fallbackState input) :=
  gasSteps_fromEntry_miss input hsize (by
    intro hz
    exact hne ((scanAcc_zero_iff_eq input hsize).1 hz))

def gasSteps_size_miss (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 376) :
    GasSteps (size376Entry input) (fallbackState input) :=
  sound sizePath (run_size_fail input hfit hsize)

def gasSteps_hit :
    GasSteps (size376Entry patterned376Input) (returnedState patterned376Input) :=
  (sound sizePath (run_size_match patterned376Input patterned376Input_size)).trans
    ((sound enterPath (run_enter patterned376Input)).trans
      gasSteps_patterned376)

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hne : input ≠ patterned376Input) :
    GasSteps (size376Entry input) (fallbackState input) := by
  by_cases hsize : input.size = 376
  · exact (sound sizePath (run_size_match input hsize)).trans
      ((sound enterPath (run_enter input)).trans
        (gasSteps_patterned376_miss input hsize hne))
  · exact gasSteps_size_miss input hfit hsize

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan
