import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop00
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop01
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop02
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop03
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop04
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop05
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop06
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop07
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop08

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

def gasSteps_loop (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 0) (loopExitState input) :=
  (((((((((gasSteps_block_0 input hsize).trans (gasSteps_block_1 input hsize)).trans (gasSteps_block_2 input hsize)).trans (gasSteps_block_3 input hsize)).trans (gasSteps_block_4 input hsize)).trans (gasSteps_block_5 input hsize)).trans (gasSteps_block_6 input hsize)).trans (gasSteps_block_7 input hsize)).trans (gasSteps_block_8 input hsize)).trans
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
