import Challenge.Modexp.Submission.Proofs.Fast.CarryFullSpecializedFour
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullSpecializedEight
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullBase
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowLemmas
import Challenge.Modexp.Submission.Proofs.Fast.CarryEntryLemmas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The multiply kernel for eligible widths only (M9 width-chain narrowing, layer W1)

Drop-in module: copy to `Challenge/Modexp/Submission/Proofs/Fast/CarryFullFast.lean` (checked here as
`M9Width.CarryFullFast`; only the module name differs).  It is the
`CarryFullToCsub` / `CarryFullMonproCsub` / `CarryFullMonproFinal` chain with the
`¬ eligible` branch removed: every statement is the tree's own statement plus ONE hypothesis
`he : StagedOperand.eligible mem n` (resp. `mem (p + 2)`), and the proofs are the eligible
branch of the originals verbatim.  It imports neither `CarryFullFallback` nor the fallback
family of `Cios2Dispatch` nor the trace layer of `Monpro`; once `ExpSubs` uses it
(layer W2), `SquareFull`, `CarryFullFallback`, `CarryFullToCsub`, `CarryFullMonproCsub`,
`CarryFullMonproFinal`, `CarryFullCsub`, `CarryFull` and the Monpro trace layer are
unreferenced from the live proof.

## Definitions assumed (imports only; signatures as they stand in the tree)

* `CarryFull.gasSteps_specializedFour / gasSteps_specializedEight (L : RowLemmas)
    (E : EntryLemmas) s mem pa pb pdst ret rest hcap hrun hcode hfork hnp hact hpa hpaFit hpb
    hpbFit hcds hs32 htl hml (hminv : inverseInvariant mem 4|8)
    (hguard : readWord mem 2720 ≠ ofNat 1) : GasSteps (dispatchState s mem pa pb pdst ret rest)
    (mpCsubState s (rowsCarry (mpZeroed s (stage mem pa n) n) pa pb n n) pdst ret rest)`
  (CarryFullSpecializedFour/Eight.lean)
* `CarryFull.readWord_selected_preserved` (CarryFullBase.lean), `CarryFull.rowLemmas`
  (CarryRowLemmas.lean), `CarryFull.entryLemmas` (CarryEntryLemmas.lean)
* `StagedOperand.eligible mem n := (n = 4 ∨ n = 8) ∧ readWord mem 2720 ≠ ofNat 1`,
  `inputMemory`, `eligible_zeroed`, `eligible_inputMemory`, `fastRepresents_inputMemory`,
  `read_inputMemory_outside` (StagedOperandMemory.lean)
* `CarryResult.selectedRows` (`if eligible mem n then rowsCarry … else rowsMem …`),
  `selectedRows_agree` (CarryResult.lean); `CarryScratchAgreement.readWord_eq`
* `Monpro.mpZeroed`, `Monpro.mpCsubState`, `Monpro.monpro_tn_le_one` (Monpro.lean, MODEL layer:
  `monpro_tn_le_one` is proved from `rows_invariant`; if the trace cut removes it, use
  `StagedMonpro.monpro_tn_le_one`, whose `hpaFit` is the weaker `… ∨ 2368 ≤ pa`)
* `Cios2Dispatch.dispatchState` (Cios2Dispatch.lean, survives the fallback-family cut)
* `Csub.gasSteps_csub`, `Csub.csStep_readWord_disjoint`, `Csub.csReturnedState`
* `CiosCachedMidMemory.inverseInvariant`

Exactly the tree's module options (`maxRecDepth 40000`, `maxHeartbeats 4000000`); no placeholder proofs,
no axiom declaration, no `native_decide`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CiosCachedMidMemory CarryIface
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult StagedOperand

-- DELETED with the 3209 multiply-entry cone: `gasSteps_toCsubFast`,
-- `gasSteps_monproCsubFast`, `gasSteps_monproFullOfFast` and `gasSteps_monproFullFast`.
--
-- All four began at `Cios2Dispatch.dispatchState`, the `MONPRO` call state at pc 3209, and
-- all four routed through `EntryLemmas.gasSteps_mulEntry`, which located a
-- `JUMPDEST; PUSH2 <mul row head>` block at instruction 2386.  That block is ABSENT from
-- this artifact -- not moved, absent.  Its `PUSH2` was HOISTED into the fused frame program
-- at pc 3414..3454, and the head it pushed, 3465, is pushed EXACTLY ONCE in the whole
-- 5,428-byte program, there, at instruction 2766.  Independently: instruction 2386 is
-- pc 2919; pc 3209 decodes to `ISZERO`; and `common` (pc 3327) is entered from exactly one
-- site in the artifact, which is the SQUARE call.  There is no multiply entry to renumber.
--
-- The only consumer was `ExpSubs.subsMonpro` -> `Exp.Subroutines.monpro`, which had ZERO
-- consumers tree-wide after the unaccelerated per-square route was removed.  `rowLemmas`
-- and the row family survive -- `FusedProductTrace` still uses `gasSteps_rowsFour/Eight`.

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull

