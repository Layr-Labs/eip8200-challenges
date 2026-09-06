import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoopMore
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoopLast
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanExitHit
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanExitMiss
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanReturn

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedScanLogic

private def gasSteps_loop (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 0) (loopExitState input) := by
  let step : ∀ n, n < 999 → GasSteps (loopState input n) (loopState input (n + 1)) :=
    fun n hn => sound loopPath (run_loop_more input n hn (by rw [hsize]; omega))
  exact (GasSteps.iterateBounded 999 step).trans
    (sound loopPath (run_loop_last input (by rw [hsize]; decide)))

def gasSteps_fromEntry_hit (input : ByteArray) (hsize : input.size = 1000)
    (hz : scanAcc input 1000 = 0) :
    GasSteps (patternedEntry input) (returnedState input) :=
  (gasSteps_loop input hsize).trans
    ((sound exitPath (run_exit_hit input hz)).trans
      (by
        have h := scanAcc_zero_iff_eq input hsize |>.1 hz
        subst input
        exact sound returnPath run_return))

def gasSteps_fromEntry_miss (input : ByteArray) (hsize : input.size = 1000)
    (hne : scanAcc input 1000 ≠ 0) :
    GasSteps (patternedEntry input) (fallbackState input) :=
  (gasSteps_loop input hsize).trans
    (sound exitPath (run_exit_miss input hne))

def gasSteps_patterned :
    GasSteps (patternedEntry patternedInput) (returnedState patternedInput) :=
  gasSteps_fromEntry_hit patternedInput patternedInput_size
    (scanAcc_patterned 1000 (by decide))

def gasSteps_patterned_miss (input : ByteArray) (hsize : input.size = 1000)
    (hne : input ≠ patternedInput) :
    GasSteps (patternedEntry input) (fallbackState input) :=
  gasSteps_fromEntry_miss input hsize (by
    intro hz
    exact hne ((scanAcc_zero_iff_eq input hsize).1 hz))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
