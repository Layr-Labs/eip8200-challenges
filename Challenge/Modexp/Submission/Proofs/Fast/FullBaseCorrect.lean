import Challenge.Modexp.Submission.Proofs.Bytecode.FullBaseHitTrace
import Challenge.Modexp.Submission.Proofs.Fast.FullBaseValueBridge
import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectCorrect

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

/-!
# Full-width-base dispatcher closure

This module restores the public `handled_of_baseHead` boundary after pc1639
was redirected. A miss reuses the relocated legacy Horner proof; a hit copies
the exact full-width base, converts it with RR as the reduced first operand,
and rejoins the exponent tail while retaining the raw base in ACC.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Exp

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

