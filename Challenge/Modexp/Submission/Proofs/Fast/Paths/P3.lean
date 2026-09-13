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
  [opAt 633 .JUMPDEST,
   pushAt 634 2 2688,
   opAt 635 .MLOAD,
   pushAt 636 2 1024,
   pushAt 637 2 1280,
   opAt 638 .MCOPY,
   pushAt 639 2 2438,
   pushAt 640 2 1280,
   pushAt 641 2 2799,
   opAt 642 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 643 .JUMPDEST,
   pushAt 644 2 933,
   pushAt 645 2 1536,
   opAt 646 (.Dup ⟨0, by decide⟩),
   pushAt 647 2 1536,
   pushAt 648 2 3552,
   opAt 649 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 650 .JUMPDEST,
   opAt 651 (.Dup ⟨2, by decide⟩),
   opAt 652 (.Dup ⟨1, by decide⟩),
   opAt 653 .SHR,
   pushAt 654 1 1,
   opAt 655 .AND,
   pushAt 656 2 256,
   opAt 657 .MUL,
   pushAt 658 2 1024,
   opAt 659 .ADD,
   pushAt 660 2 1744,
   opAt 661 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 662 .JUMPDEST,
   opAt 663 .POP,
   opAt 664 (.Dup ⟨0, by decide⟩),
   opAt 665 .ISZERO,
   pushAt 666 2 967,
   opAt 667 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 668 0 0,
   opAt 669 .NOT,
   opAt 670 .ADD,
   pushAt 671 2 918,
   opAt 672 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 673 .JUMPDEST,
   opAt 674 .POP,
   opAt 675 (.Dup ⟨2, by decide⟩),
   opAt 676 .ISZERO,
   pushAt 677 2 2682,
   opAt 678 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
