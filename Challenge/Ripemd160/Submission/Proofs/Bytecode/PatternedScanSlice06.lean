import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_slice_174 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 174) (loopState input 203) :=
  gasSteps_loop_slice input hsize 174 29 (by decide)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
