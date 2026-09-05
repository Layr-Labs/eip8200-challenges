import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice00
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice01
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice02
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice03
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice04
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice05
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice06

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_chain_0 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 0) (loopState input 203) :=
  (((((((gasSteps_slice_0 input hsize).trans (gasSteps_slice_29 input hsize)).trans (gasSteps_slice_58 input hsize)).trans (gasSteps_slice_87 input hsize)).trans (gasSteps_slice_116 input hsize)).trans (gasSteps_slice_145 input hsize)).trans (gasSteps_slice_174 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
