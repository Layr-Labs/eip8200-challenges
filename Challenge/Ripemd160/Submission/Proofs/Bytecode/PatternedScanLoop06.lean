import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_slice_696 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 696) (loopState input 725) :=
  gasSteps_loop_slice input hsize 696 29 (by decide)

theorem gasSteps_slice_725 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 725) (loopState input 754) :=
  gasSteps_loop_slice input hsize 725 29 (by decide)

theorem gasSteps_slice_754 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 754) (loopState input 783) :=
  gasSteps_loop_slice input hsize 754 29 (by decide)

theorem gasSteps_slice_783 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 783) (loopState input 812) :=
  gasSteps_loop_slice input hsize 783 29 (by decide)

theorem gasSteps_block_6 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 696) (loopState input 812) :=
  ((((gasSteps_slice_696 input hsize).trans (gasSteps_slice_725 input hsize)).trans (gasSteps_slice_754 input hsize)).trans (gasSteps_slice_783 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
