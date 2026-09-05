import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_slice_348 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 348) (loopState input 377) :=
  gasSteps_loop_slice input hsize 348 29 (by decide)

theorem gasSteps_slice_377 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 377) (loopState input 406) :=
  gasSteps_loop_slice input hsize 377 29 (by decide)

theorem gasSteps_slice_406 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 406) (loopState input 435) :=
  gasSteps_loop_slice input hsize 406 29 (by decide)

theorem gasSteps_slice_435 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 435) (loopState input 464) :=
  gasSteps_loop_slice input hsize 435 29 (by decide)

theorem gasSteps_block_3 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 348) (loopState input 464) :=
  ((((gasSteps_slice_348 input hsize).trans (gasSteps_slice_377 input hsize)).trans (gasSteps_slice_406 input hsize)).trans (gasSteps_slice_435 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
