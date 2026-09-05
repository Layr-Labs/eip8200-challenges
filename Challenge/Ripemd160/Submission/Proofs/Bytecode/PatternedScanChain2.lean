import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice14
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice15
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice16
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice17
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice18
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice19
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanSlice20

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

theorem gasSteps_chain_2 (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 406) (loopState input 609) :=
  (((((((gasSteps_slice_406 input hsize).trans (gasSteps_slice_435 input hsize)).trans (gasSteps_slice_464 input hsize)).trans (gasSteps_slice_493 input hsize)).trans (gasSteps_slice_522 input hsize)).trans (gasSteps_slice_551 input hsize)).trans (gasSteps_slice_580 input hsize))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
