import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_slice_580 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 580) (loopState input 609) :=
  gasSteps_loop_slice input hsize 580 29 (by decide)

theorem gasSteps_slice_609 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 609) (loopState input 638) :=
  gasSteps_loop_slice input hsize 609 29 (by decide)

theorem gasSteps_slice_638 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 638) (loopState input 667) :=
  gasSteps_loop_slice input hsize 638 29 (by decide)

theorem gasSteps_slice_667 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 667) (loopState input 696) :=
  gasSteps_loop_slice input hsize 667 29 (by decide)

theorem gasSteps_block_5 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 580) (loopState input 696) :=
  ((((gasSteps_slice_580 input hsize).trans (gasSteps_slice_609 input hsize)).trans (gasSteps_slice_638 input hsize)).trans (gasSteps_slice_667 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
