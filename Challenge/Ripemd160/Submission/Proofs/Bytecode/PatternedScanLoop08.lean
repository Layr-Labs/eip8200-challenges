import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_slice_928 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 928) (loopState input 957) :=
  gasSteps_loop_slice input hsize 928 29 (by decide)

theorem gasSteps_slice_957 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 957) (loopState input 986) :=
  gasSteps_loop_slice input hsize 957 29 (by decide)

theorem gasSteps_slice_986 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 986) (loopState input 999) :=
  gasSteps_loop_slice input hsize 986 13 (by decide)

theorem gasSteps_block_8 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 928) (loopState input 999) :=
  (((gasSteps_slice_928 input hsize).trans (gasSteps_slice_957 input hsize)).trans (gasSteps_slice_986 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
