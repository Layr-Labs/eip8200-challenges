import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanChain0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanChain1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanChain2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanChain3
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanChain4

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

def gasSteps_loop (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 0) (loopExitState input) :=
  (((((gasSteps_chain_0 input hsize).trans (gasSteps_chain_1 input hsize)).trans (gasSteps_chain_2 input hsize)).trans (gasSteps_chain_3 input hsize)).trans (gasSteps_chain_4 input hsize)).trans
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
