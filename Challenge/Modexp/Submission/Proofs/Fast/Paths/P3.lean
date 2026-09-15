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
  [opAt 564 .JUMPDEST,
   pushAt 565 2 2688,
   opAt 566 .MLOAD,
   pushAt 567 2 1024,
   pushAt 568 2 1280,
   opAt 569 .MCOPY,
   pushAt 570 2 2009,
   pushAt 571 2 1280,
   pushAt 572 2 2298,
   opAt 573 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 574 .JUMPDEST,
   pushAt 575 2 819,
   pushAt 576 2 1536,
   opAt 577 (.Dup ⟨0, by decide⟩),
   pushAt 578 2 1536,
   pushAt 579 2 3209,
   opAt 580 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 581 .JUMPDEST,
   opAt 582 (.Dup ⟨2, by decide⟩),
   opAt 583 (.Dup ⟨1, by decide⟩),
   opAt 584 .SHR,
   pushAt 585 1 1,
   opAt 586 .AND,
   pushAt 587 1 8,
   opAt 588 .SHL,
   pushAt 589 2 1024,
   opAt 590 .ADD,
   pushAt 591 2 1348,
   opAt 592 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 593 .JUMPDEST,
   opAt 594 .POP,
   opAt 595 (.Dup ⟨0, by decide⟩),
   opAt 596 .ISZERO,
   pushAt 597 2 852,
   opAt 598 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 599 0 0,
   opAt 600 .NOT,
   opAt 601 .ADD,
   pushAt 602 2 804,
   opAt 603 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 604 .JUMPDEST,
   opAt 605 .POP,
   opAt 606 (.Dup ⟨2, by decide⟩),
   opAt 607 .ISZERO,
   pushAt 608 2 2182,
   opAt 609 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
