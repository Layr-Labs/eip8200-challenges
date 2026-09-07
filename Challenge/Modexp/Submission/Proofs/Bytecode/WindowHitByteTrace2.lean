import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteSlices
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleLookup

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteTrace2

open Challenge.EvmProof.Stepper
open EvmSemantics
open EvmSemantics.EVM
open WindowHitByteSlices
open WindowByteKernel
open WindowNibbleKernel

/-! The high square and lookup are fused in `WindowHitByteTrace1`. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteTrace2
