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

/-!
Byte 0 has no standalone high-nibble lookup block. The four squares and the
table multiply are fused in `WindowHitByteTrace1.run_byte0_highSquareLookup`
(`2853 → 2872`); the low-nibble fusion lives in
`WindowHitByteTrace3.run_byte0_lowSquareLookup` (`2877 → 2896`). This module
is kept as an import-compatible placeholder. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteTrace2
