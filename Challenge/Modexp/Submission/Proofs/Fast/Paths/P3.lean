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
  [opAt 626 .JUMPDEST,
   pushAt 627 2 2688,
   opAt 628 .MLOAD,
   pushAt 629 2 1024,
   pushAt 630 2 1280,
   opAt 631 .MCOPY,
   pushAt 632 2 2395,
   pushAt 633 2 1280,
   pushAt 634 2 2754,
   opAt 635 .JUMP]

/-- Instructions 1282..1202, pc 1680..1692. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1289..1295, pc 1569..1662. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 636 .JUMPDEST,
   pushAt 637 2 918,
   pushAt 638 2 1536,
   opAt 639 (.Dup ⟨0, by decide⟩),
   pushAt 640 2 1536,
   pushAt 641 2 3550,
   opAt 642 .JUMP]

/-- Instructions 1296..1307, pc 1713..1599. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 643 .JUMPDEST,
   opAt 644 (.Dup ⟨2, by decide⟩),
   opAt 645 (.Dup ⟨1, by decide⟩),
   opAt 646 .SHR,
   pushAt 647 1 1,
   opAt 648 .AND,
   pushAt 649 1 8,
   opAt 650 .SHL,
   pushAt 651 2 1024,
   opAt 652 .ADD,
   pushAt 653 2 1728,
   opAt 654 .JUMP]

/-- Instructions 1178..1269, pc 1692..1749. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 655 .JUMPDEST,
   opAt 656 .POP,
   opAt 657 (.Dup ⟨0, by decide⟩),
   opAt 658 .ISZERO,
   pushAt 659 2 951,
   opAt 660 .JUMPI]

/-- Instructions 1184..1188, pc 1750..1760. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 661 0 0,
   opAt 662 .NOT,
   opAt 663 .ADD,
   pushAt 664 2 903,
   opAt 665 .JUMP]

/-- Instructions 1323..1324, pc 1758..1717. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 666 .JUMPDEST,
   opAt 667 .POP,
   opAt 668 (.Dup ⟨2, by decide⟩),
   opAt 669 .ISZERO,
   pushAt 670 2 2638,
   opAt 671 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
