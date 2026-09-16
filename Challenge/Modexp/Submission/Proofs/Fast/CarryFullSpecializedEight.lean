import Challenge.Modexp.Submission.Proofs.Fast.CarryFullRowsEight

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CiosCachedMidMemory CarryIface
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult StagedOperand

-- DELETED with the 3209 multiply-entry cone.  This routine began at
-- `Cios2Dispatch.dispatchState` (pc 3209) and its first step was
-- `E.gasSteps_mulEntry`, which located a `JUMPDEST; PUSH2 <mul row head>` block at
-- instruction 2386.  That block is ABSENT from this artifact: the `PUSH2` was HOISTED into
-- the fused frame program at pc 3414..3454, where the single `PUSH2 3465` in the whole
-- 5,428-byte program sits (instruction 2766).  Instruction 2386 is pc 2919; pc 3209 is
-- `ISZERO`; `common` at pc 3327 is entered from exactly one site, the SQUARE call.
-- Absence of code, not a wrong constant -- there was nothing to renumber it to.
-- Its only consumer was `CarryFullFast`, deleted with it, and that chain ended at
-- `Exp.Subroutines.monpro`, which had zero consumers tree-wide.


end Challenge.Modexp.Submission.Proofs.Fast.CarryFull
