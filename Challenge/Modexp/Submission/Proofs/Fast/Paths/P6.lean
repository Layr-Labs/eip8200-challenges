import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 6 (instructions 1396..1368). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 566 .JUMPDEST,
   opAt 567 (.Dup ⟨4, by decide⟩),
   opAt 568 (.Dup ⟨0, by decide⟩),
   opAt 569 (.Dup ⟨2, by decide⟩),
   pushAt 570 2 256,
   opAt 571 .ADD,
   opAt 572 .SUB,
   opAt 573 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 574 .JUMPDEST,
   opAt 575 .POP,
   pushAt 576 2 553,
   opAt 577 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 715..717, pc 1053..1056: the six-word bail.  The wide-modulus
fallback re-reads the header itself, so the live words are no longer dropped and the
block jumps straight to the fallback entry at pc 236. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 578 .JUMPDEST,
   pushAt 579 1 238,
   opAt 580 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
