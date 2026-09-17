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
  [opAt 560 .JUMPDEST,
   pushAt 561 2 2688,
   opAt 562 .MLOAD,
   pushAt 563 2 1024,
   pushAt 564 2 1280,
   opAt 565 .MCOPY,
   pushAt 566 2 2009,
   pushAt 567 2 1280,
   pushAt 568 2 2298,
   opAt 569 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 570 .JUMPDEST,
   pushAt 571 2 819,
   pushAt 572 2 1536,
   opAt 573 (.Dup ⟨0, by decide⟩),
   pushAt 574 2 1536,
   pushAt 575 2 3209,
   opAt 576 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 577 .JUMPDEST,
   opAt 578 (.Dup ⟨2, by decide⟩),
   opAt 579 (.Dup ⟨1, by decide⟩),
   opAt 580 .SHR,
   pushAt 581 1 1,
   opAt 582 .AND,
   pushAt 583 1 8,
   opAt 584 .SHL,
   pushAt 585 2 1024,
   opAt 586 .ADD,
   pushAt 587 2 1348,
   opAt 588 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 589 .JUMPDEST,
   opAt 590 .POP,
   opAt 591 (.Dup ⟨0, by decide⟩),
   opAt 592 .ISZERO,
   pushAt 593 2 852,
   opAt 594 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 595 0 0,
   opAt 596 .NOT,
   opAt 597 .ADD,
   pushAt 598 2 804,
   opAt 599 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 600 .JUMPDEST,
   opAt 601 .POP,
   opAt 602 (.Dup ⟨2, by decide⟩),
   opAt 603 .ISZERO,
   pushAt 604 2 2182,
   opAt 605 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
