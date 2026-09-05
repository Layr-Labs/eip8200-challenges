import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice28
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice29
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice30
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice31
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice32
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice33
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice34

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_chain_4 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 812) (loopState input 999) :=
  (((((((gasSteps_slice_812 input hsize).trans (gasSteps_slice_841 input hsize)).trans (gasSteps_slice_870 input hsize)).trans (gasSteps_slice_899 input hsize)).trans (gasSteps_slice_928 input hsize)).trans (gasSteps_slice_957 input hsize)).trans (gasSteps_slice_986 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
