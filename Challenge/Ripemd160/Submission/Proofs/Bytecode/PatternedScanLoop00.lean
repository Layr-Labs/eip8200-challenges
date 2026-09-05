import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_slice_0 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 0) (loopState input 29) :=
  gasSteps_loop_slice input hsize 0 29 (by decide)

theorem gasSteps_slice_29 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 29) (loopState input 58) :=
  gasSteps_loop_slice input hsize 29 29 (by decide)

theorem gasSteps_slice_58 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 58) (loopState input 87) :=
  gasSteps_loop_slice input hsize 58 29 (by decide)

theorem gasSteps_slice_87 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 87) (loopState input 116) :=
  gasSteps_loop_slice input hsize 87 29 (by decide)

theorem gasSteps_block_0 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 0) (loopState input 116) :=
  ((((gasSteps_slice_0 input hsize).trans (gasSteps_slice_29 input hsize)).trans (gasSteps_slice_58 input hsize)).trans (gasSteps_slice_87 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
