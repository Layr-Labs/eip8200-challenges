import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 5 (instructions 1385..1395). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1385..1393, pc 1863..1833. -/
def blk1255 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 646 .JUMPDEST,
   opAt 647 .POP,
   opAt 648 .POP,
   pushAt 649 2 2182,
   pushAt 650 2 512,
   pushAt 651 2 1536,
   pushAt 652 2 256,
   pushAt 653 2 3209,
   opAt 654 .JUMP]

/-- Instructions 1402..1360, pc 1896..1904. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 655 .JUMPDEST,
   opAt 656 (.Dup ⟨4, by decide⟩),
   opAt 657 (.Dup ⟨1, by decide⟩),
   opAt 658 .EQ,
   pushAt 659 2 1021,
   opAt 660 .JUMPI]

/-- Instructions 1409..1416, pc 1905..1914. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 661 2 1299,
   opAt 662 .JUMP]

/-- Instructions 1417..1423, pc 1916..1932. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 663 .JUMPDEST,
   pushAt 664 2 977,
   pushAt 665 2 256,
   opAt 666 (.Dup ⟨0, by decide⟩),
   pushAt 667 2 256,
   pushAt 668 2 3209,
   opAt 669 .JUMP]

/-- Instructions 1424..1430, pc 1933..1941. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 670 .JUMPDEST,
   opAt 671 (.Dup ⟨1, by decide⟩),
   opAt 672 (.Dup ⟨1, by decide⟩),
   opAt 673 .AND,
   opAt 674 .ISZERO,
   pushAt 675 2 1003,
   opAt 676 .JUMPI]

/-- Instructions 1431..1388, pc 1942..1957. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 677 2 1002,
   pushAt 678 2 256,
   pushAt 679 2 512,
   pushAt 680 2 256,
   pushAt 681 2 3209,
   opAt 682 .JUMP]

/-- Instructions 1389..1389, pc 1958..1958. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 683 .JUMPDEST]

/-- Instructions 1438..1395, pc 1829..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 684 .JUMPDEST,
   pushAt 685 1 1,
   opAt 686 .SHR,
   opAt 687 (.Dup ⟨0, by decide⟩),
   pushAt 688 2 962,
   opAt 689 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
