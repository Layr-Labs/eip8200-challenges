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
  [opAt 638 .JUMPDEST,
   opAt 639 .POP,
   opAt 640 .POP,
   pushAt 641 2 2439,
   pushAt 642 2 512,
   pushAt 643 2 1536,
   pushAt 644 2 256,
   pushAt 645 2 3349,
   opAt 646 .JUMP]

/-- Instructions 1402..1360, pc 1896..1904. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 647 .JUMPDEST,
   opAt 648 (.Dup ⟨4, by decide⟩),
   opAt 649 (.Dup ⟨1, by decide⟩),
   opAt 650 .EQ,
   pushAt 651 2 1009,
   opAt 652 .JUMPI]

/-- Instructions 1409..1416, pc 1905..1914. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 653 2 1561,
   opAt 654 .JUMP]

/-- Instructions 1417..1423, pc 1916..1932. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 655 .JUMPDEST,
   pushAt 656 2 964,
   pushAt 657 2 256,
   opAt 658 (.Dup ⟨0, by decide⟩),
   pushAt 659 2 256,
   pushAt 660 2 3349,
   opAt 661 .JUMP]

/-- Instructions 1424..1430, pc 1933..1941. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 662 .JUMPDEST,
   opAt 663 (.Dup ⟨1, by decide⟩),
   opAt 664 (.Dup ⟨1, by decide⟩),
   opAt 665 .AND,
   opAt 666 .ISZERO,
   pushAt 667 2 990,
   opAt 668 .JUMPI]

/-- Instructions 1431..1388, pc 1942..1957. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 669 2 989,
   pushAt 670 2 256,
   pushAt 671 2 512,
   pushAt 672 2 256,
   pushAt 673 2 3349,
   opAt 674 .JUMP]

/-- Instructions 1389..1389, pc 1958..1958. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 675 .JUMPDEST]

/-- Instructions 1438..1395, pc 1829..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 676 .JUMPDEST,
   pushAt 677 2 1,
   opAt 678 .SHR,
   opAt 679 (.Dup ⟨0, by decide⟩),
   pushAt 680 2 949,
   opAt 681 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
