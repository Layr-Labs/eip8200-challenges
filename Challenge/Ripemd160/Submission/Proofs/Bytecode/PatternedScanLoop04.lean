import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_slice_464 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 464) (loopState input 493) :=
  gasSteps_loop_slice input hsize 464 29 (by decide)

theorem gasSteps_slice_493 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 493) (loopState input 522) :=
  gasSteps_loop_slice input hsize 493 29 (by decide)

theorem gasSteps_slice_522 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 522) (loopState input 551) :=
  gasSteps_loop_slice input hsize 522 29 (by decide)

theorem gasSteps_slice_551 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 551) (loopState input 580) :=
  gasSteps_loop_slice input hsize 551 29 (by decide)

theorem gasSteps_block_4 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 464) (loopState input 580) :=
  ((((gasSteps_slice_464 input hsize).trans (gasSteps_slice_493 input hsize)).trans (gasSteps_slice_522 input hsize)).trans (gasSteps_slice_551 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
