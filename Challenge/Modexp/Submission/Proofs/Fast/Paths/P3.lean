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
  [opAt 554 .JUMPDEST,
   pushAt 555 2 2688,
   opAt 556 .MLOAD,
   pushAt 557 2 1024,
   pushAt 558 2 1280,
   opAt 559 .MCOPY,
   pushAt 560 2 2270,
   pushAt 561 2 1280,
   pushAt 562 2 2559,
   opAt 563 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 564 .JUMPDEST,
   pushAt 565 2 808,
   pushAt 566 2 1536,
   opAt 567 (.Dup ⟨0, by decide⟩),
   pushAt 568 2 1536,
   pushAt 569 2 3353,
   opAt 570 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 571 .JUMPDEST,
   opAt 572 (.Dup ⟨2, by decide⟩),
   opAt 573 (.Dup ⟨1, by decide⟩),
   opAt 574 .SHR,
   pushAt 575 1 1,
   opAt 576 .AND,
   pushAt 577 1 8,
   opAt 578 .SHL,
   pushAt 579 2 1024,
   opAt 580 .ADD,
   pushAt 581 2 1609,
   opAt 582 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 583 .JUMPDEST,
   opAt 584 .POP,
   opAt 585 (.Dup ⟨0, by decide⟩),
   opAt 586 .ISZERO,
   pushAt 587 2 841,
   opAt 588 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 589 0 0,
   opAt 590 .NOT,
   opAt 591 .ADD,
   pushAt 592 2 793,
   opAt 593 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 594 .JUMPDEST,
   opAt 595 .POP,
   opAt 596 (.Dup ⟨2, by decide⟩),
   opAt 597 .ISZERO,
   pushAt 598 2 2443,
   opAt 599 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
