import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 3 (instructions 1186..1324). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1186..1229, pc 1610..1679. -/
def blk1138 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 552 .JUMPDEST,
   pushAt 553 2 2688,
   opAt 554 .MLOAD,
   pushAt 555 2 1024,
   pushAt 556 2 1280,
   opAt 557 .MCOPY,
   pushAt 558 2 2266,
   pushAt 559 2 1280,
   pushAt 560 2 2555,
   opAt 561 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 562 .JUMPDEST,
   pushAt 563 2 806,
   pushAt 564 2 1536,
   opAt 565 (.Dup ⟨0, by decide⟩),
   pushAt 566 2 1536,
   pushAt 567 2 3349,
   opAt 568 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 569 .JUMPDEST,
   opAt 570 (.Dup ⟨2, by decide⟩),
   opAt 571 (.Dup ⟨1, by decide⟩),
   opAt 572 .SHR,
   pushAt 573 1 1,
   opAt 574 .AND,
   pushAt 575 1 8,
   opAt 576 .SHL,
   pushAt 577 2 1024,
   opAt 578 .ADD,
   pushAt 579 2 1610,
   opAt 580 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 581 .JUMPDEST,
   opAt 582 .POP,
   opAt 583 (.Dup ⟨0, by decide⟩),
   opAt 584 .ISZERO,
   pushAt 585 2 839,
   opAt 586 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 587 0 0,
   opAt 588 .NOT,
   opAt 589 .ADD,
   pushAt 590 2 791,
   opAt 591 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 592 .JUMPDEST,
   opAt 593 .POP,
   opAt 594 (.Dup ⟨2, by decide⟩),
   opAt 595 .ISZERO,
   pushAt 596 2 2439,
   opAt 597 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
