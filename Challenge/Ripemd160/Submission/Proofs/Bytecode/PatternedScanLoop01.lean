import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_slice_116 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 116) (loopState input 145) :=
  gasSteps_loop_slice input hsize 116 29 (by decide)

theorem gasSteps_slice_145 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 145) (loopState input 174) :=
  gasSteps_loop_slice input hsize 145 29 (by decide)

theorem gasSteps_slice_174 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 174) (loopState input 203) :=
  gasSteps_loop_slice input hsize 174 29 (by decide)

theorem gasSteps_slice_203 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 203) (loopState input 232) :=
  gasSteps_loop_slice input hsize 203 29 (by decide)

theorem gasSteps_block_1 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 116) (loopState input 232) :=
  ((((gasSteps_slice_116 input hsize).trans (gasSteps_slice_145 input hsize)).trans (gasSteps_slice_174 input hsize)).trans (gasSteps_slice_203 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
