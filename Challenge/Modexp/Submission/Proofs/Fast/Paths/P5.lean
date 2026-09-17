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
  [opAt 650 .JUMPDEST,
   opAt 651 .POP,
   opAt 652 .POP,
   pushAt 653 2 2182,
   pushAt 654 2 512,
   pushAt 655 2 1536,
   pushAt 656 2 256,
   pushAt 657 2 3209,
   opAt 658 .JUMP]

/-- Instructions 1402..1360, pc 1896..1904. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 659 .JUMPDEST,
   opAt 660 (.Dup ⟨4, by decide⟩),
   opAt 661 (.Dup ⟨1, by decide⟩),
   opAt 662 .EQ,
   pushAt 663 2 1021,
   opAt 664 .JUMPI]

/-- Instructions 1409..1416, pc 1905..1914. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 665 2 1299,
   opAt 666 .JUMP]

/-- Instructions 1417..1423, pc 1916..1932. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 667 .JUMPDEST,
   pushAt 668 2 977,
   pushAt 669 2 256,
   opAt 670 (.Dup ⟨0, by decide⟩),
   pushAt 671 2 256,
   pushAt 672 2 3209,
   opAt 673 .JUMP]

/-- Instructions 1424..1430, pc 1933..1941. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 674 .JUMPDEST,
   opAt 675 (.Dup ⟨1, by decide⟩),
   opAt 676 (.Dup ⟨1, by decide⟩),
   opAt 677 .AND,
   opAt 678 .ISZERO,
   pushAt 679 2 1003,
   opAt 680 .JUMPI]

/-- Instructions 1431..1388, pc 1942..1957. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 681 2 1002,
   pushAt 682 2 256,
   pushAt 683 2 512,
   pushAt 684 2 256,
   pushAt 685 2 3209,
   opAt 686 .JUMP]

/-- Instructions 1389..1389, pc 1958..1958. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 687 .JUMPDEST]

/-- Instructions 1438..1395, pc 1829..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 688 .JUMPDEST,
   pushAt 689 1 1,
   opAt 690 .SHR,
   opAt 691 (.Dup ⟨0, by decide⟩),
   pushAt 692 2 962,
   opAt 693 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
