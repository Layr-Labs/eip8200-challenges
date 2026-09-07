import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! The 13-instruction selector at instructions 1412..1424 and pc 1982..2003,
inserted before the generic row landing. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Select the fixed H2 entry for four- and eight-limb rows, then fall through
to the generic row landing for all other sizes. -/
def blk1412 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1412 2 9344,
   opAt 1413 .MLOAD,
   opAt 1414 (.Dup ⟨0, by decide⟩),
   pushAt 1415 1 128,
   opAt 1416 .EQ,
   pushAt 1417 2 5515,
   opAt 1418 .JUMPI,
   opAt 1419 (.Dup ⟨0, by decide⟩),
   pushAt 1420 2 256,
   opAt 1421 .EQ,
   pushAt 1422 2 6668,
   opAt 1423 .JUMPI,
   opAt 1424 .POP]

def h2Selector := blk1412
def h2Selector4 := h2Selector.take 7
def h2Selector8 := h2Selector.take 12
def h2SelectorMiss := h2Selector

end Challenge.Modexp.Submission.Proofs.Fast
