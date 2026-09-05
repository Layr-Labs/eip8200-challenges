import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_slice_812 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 812) (loopState input 841) :=
  gasSteps_loop_slice input hsize 812 29 (by decide)

theorem gasSteps_slice_841 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 841) (loopState input 870) :=
  gasSteps_loop_slice input hsize 841 29 (by decide)

theorem gasSteps_slice_870 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 870) (loopState input 899) :=
  gasSteps_loop_slice input hsize 870 29 (by decide)

theorem gasSteps_slice_899 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 899) (loopState input 928) :=
  gasSteps_loop_slice input hsize 899 29 (by decide)

theorem gasSteps_block_7 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 812) (loopState input 928) :=
  ((((gasSteps_slice_812 input hsize).trans (gasSteps_slice_841 input hsize)).trans (gasSteps_slice_870 input hsize)).trans (gasSteps_slice_899 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
