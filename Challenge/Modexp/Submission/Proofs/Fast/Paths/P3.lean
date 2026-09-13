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
  [opAt 628 .JUMPDEST,
   pushAt 629 2 2688,
   opAt 630 .MLOAD,
   pushAt 631 2 1024,
   pushAt 632 2 1280,
   opAt 633 .MCOPY,
   pushAt 634 2 2438,
   pushAt 635 2 1280,
   pushAt 636 2 2799,
   opAt 637 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 638 .JUMPDEST,
   pushAt 639 2 933,
   pushAt 640 2 1536,
   opAt 641 (.Dup ⟨0, by decide⟩),
   pushAt 642 2 1536,
   pushAt 643 2 3552,
   opAt 644 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 645 .JUMPDEST,
   opAt 646 (.Dup ⟨2, by decide⟩),
   opAt 647 (.Dup ⟨1, by decide⟩),
   opAt 648 .SHR,
   pushAt 649 1 1,
   opAt 650 .AND,
   pushAt 651 2 256,
   opAt 652 .MUL,
   pushAt 653 2 1024,
   opAt 654 .ADD,
   pushAt 655 2 1744,
   opAt 656 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 657 .JUMPDEST,
   opAt 658 .POP,
   opAt 659 (.Dup ⟨0, by decide⟩),
   opAt 660 .ISZERO,
   pushAt 661 2 967,
   opAt 662 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 663 0 0,
   opAt 664 .NOT,
   opAt 665 .ADD,
   pushAt 666 2 918,
   opAt 667 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 668 .JUMPDEST,
   opAt 669 .POP,
   opAt 670 (.Dup ⟨2, by decide⟩),
   opAt 671 .ISZERO,
   pushAt 672 2 2682,
   opAt 673 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
