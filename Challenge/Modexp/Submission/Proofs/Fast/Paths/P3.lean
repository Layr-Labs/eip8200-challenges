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
  [opAt 625 .JUMPDEST,
   pushAt 626 2 2688,
   opAt 627 .MLOAD,
   pushAt 628 2 1024,
   pushAt 629 2 1280,
   opAt 630 .MCOPY,
   pushAt 631 2 2394,
   pushAt 632 2 1280,
   pushAt 633 2 2753,
   opAt 634 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 635 .JUMPDEST,
   pushAt 636 2 917,
   pushAt 637 2 1536,
   opAt 638 (.Dup ⟨0, by decide⟩),
   pushAt 639 2 1536,
   pushAt 640 2 3550,
   opAt 641 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 642 .JUMPDEST,
   opAt 643 (.Dup ⟨2, by decide⟩),
   opAt 644 (.Dup ⟨1, by decide⟩),
   opAt 645 .SHR,
   pushAt 646 1 1,
   opAt 647 .AND,
   pushAt 648 1 8,
   opAt 649 .SHL,
   pushAt 650 2 1024,
   opAt 651 .ADD,
   pushAt 652 2 1727,
   opAt 653 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 654 .JUMPDEST,
   opAt 655 .POP,
   opAt 656 (.Dup ⟨0, by decide⟩),
   opAt 657 .ISZERO,
   pushAt 658 2 950,
   opAt 659 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 660 0 0,
   opAt 661 .NOT,
   opAt 662 .ADD,
   pushAt 663 2 902,
   opAt 664 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 665 .JUMPDEST,
   opAt 666 .POP,
   opAt 667 (.Dup ⟨2, by decide⟩),
   opAt 668 .ISZERO,
   pushAt 669 2 2637,
   opAt 670 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
