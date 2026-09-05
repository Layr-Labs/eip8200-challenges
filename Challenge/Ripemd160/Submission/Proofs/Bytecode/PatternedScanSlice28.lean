import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_slice_812 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 812) (loopState input 841) :=
  gasSteps_loop_slice input hsize 812 29 (by decide)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
