import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice07
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice08
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice09
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice10
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice11
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice12
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice13

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_chain_1 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 203) (loopState input 406) :=
  (((((((gasSteps_slice_203 input hsize).trans (gasSteps_slice_232 input hsize)).trans (gasSteps_slice_261 input hsize)).trans (gasSteps_slice_290 input hsize)).trans (gasSteps_slice_319 input hsize)).trans (gasSteps_slice_348 input hsize)).trans (gasSteps_slice_377 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
