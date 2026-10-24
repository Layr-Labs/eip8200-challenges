import Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Contract for the one-word dispatch

The dispatcher sends every input with a modulus of 1..32 bytes straight to the
one-word entry at pc 135; inputs with `exponentSize = modulusSize = 32` never
reach it, because pc 0 sends them to the early fixed-width route.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowRoute

open EvmSemantics
open EvmSemantics.EVM

structure Route where
  enter : ∀ input : ByteArray, ValidInput input →
    0 < modulusSize input → modulusSize input ≤ 32 →
    Dispatch.WordRouteEnter input

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowRoute
