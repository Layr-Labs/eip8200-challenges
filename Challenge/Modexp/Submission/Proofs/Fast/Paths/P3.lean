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
  [opAt 627 .JUMPDEST,
   pushAt 628 2 2688,
   opAt 629 .MLOAD,
   pushAt 630 2 1024,
   pushAt 631 2 1280,
   opAt 632 .MCOPY,
   pushAt 633 2 2394,
   pushAt 634 2 1280,
   pushAt 635 2 2753,
   opAt 636 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 637 .JUMPDEST,
   pushAt 638 2 918,
   pushAt 639 2 1536,
   opAt 640 (.Dup ⟨0, by decide⟩),
   pushAt 641 2 1536,
   pushAt 642 2 3550,
   opAt 643 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 644 .JUMPDEST,
   opAt 645 (.Dup ⟨2, by decide⟩),
   opAt 646 (.Dup ⟨1, by decide⟩),
   opAt 647 .SHR,
   pushAt 648 1 1,
   opAt 649 .AND,
   pushAt 650 1 8,
   opAt 651 .SHL,
   pushAt 652 2 1024,
   opAt 653 .ADD,
   pushAt 654 2 1728,
   opAt 655 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 656 .JUMPDEST,
   opAt 657 .POP,
   opAt 658 (.Dup ⟨0, by decide⟩),
   opAt 659 .ISZERO,
   pushAt 660 2 951,
   opAt 661 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 662 0 0,
   opAt 663 .NOT,
   opAt 664 .ADD,
   pushAt 665 2 903,
   opAt 666 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 667 .JUMPDEST,
   opAt 668 .POP,
   opAt 669 (.Dup ⟨2, by decide⟩),
   opAt 670 .ISZERO,
   pushAt 671 2 2637,
   opAt 672 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
