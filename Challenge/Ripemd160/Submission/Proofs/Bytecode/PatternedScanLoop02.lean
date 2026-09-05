import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_slice_232 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 232) (loopState input 261) :=
  gasSteps_loop_slice input hsize 232 29 (by decide)

theorem gasSteps_slice_261 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 261) (loopState input 290) :=
  gasSteps_loop_slice input hsize 261 29 (by decide)

theorem gasSteps_slice_290 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 290) (loopState input 319) :=
  gasSteps_loop_slice input hsize 290 29 (by decide)

theorem gasSteps_slice_319 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 319) (loopState input 348) :=
  gasSteps_loop_slice input hsize 319 29 (by decide)

theorem gasSteps_block_2 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 232) (loopState input 348) :=
  ((((gasSteps_slice_232 input hsize).trans (gasSteps_slice_261 input hsize)).trans (gasSteps_slice_290 input hsize)).trans (gasSteps_slice_319 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
