import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice21
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice22
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice23
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice24
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice25
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice26
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice27

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_chain_3 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 609) (loopState input 812) :=
  (((((((gasSteps_slice_609 input hsize).trans (gasSteps_slice_638 input hsize)).trans (gasSteps_slice_667 input hsize)).trans (gasSteps_slice_696 input hsize)).trans (gasSteps_slice_725 input hsize)).trans (gasSteps_slice_754 input hsize)).trans (gasSteps_slice_783 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
