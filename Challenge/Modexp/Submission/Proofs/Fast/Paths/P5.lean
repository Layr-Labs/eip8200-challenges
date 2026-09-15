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
  [opAt 640 .JUMPDEST,
   opAt 641 .POP,
   opAt 642 .POP,
   pushAt 643 2 2443,
   pushAt 644 2 512,
   pushAt 645 2 1536,
   pushAt 646 2 256,
   pushAt 647 2 3353,
   opAt 648 .JUMP]

/-- Instructions 1402..1360, pc 1896..1904. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 649 .JUMPDEST,
   opAt 650 (.Dup ⟨4, by decide⟩),
   opAt 651 (.Dup ⟨1, by decide⟩),
   opAt 652 .EQ,
   pushAt 653 2 1010,
   opAt 654 .JUMPI]

/-- Instructions 1409..1416, pc 1905..1914. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 655 2 1560,
   opAt 656 .JUMP]

/-- Instructions 1417..1423, pc 1916..1932. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 657 .JUMPDEST,
   pushAt 658 2 966,
   pushAt 659 2 256,
   opAt 660 (.Dup ⟨0, by decide⟩),
   pushAt 661 2 256,
   pushAt 662 2 3353,
   opAt 663 .JUMP]

/-- Instructions 1424..1430, pc 1933..1941. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 664 .JUMPDEST,
   opAt 665 (.Dup ⟨1, by decide⟩),
   opAt 666 (.Dup ⟨1, by decide⟩),
   opAt 667 .AND,
   opAt 668 .ISZERO,
   pushAt 669 2 992,
   opAt 670 .JUMPI]

/-- Instructions 1431..1388, pc 1942..1957. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 671 2 991,
   pushAt 672 2 256,
   pushAt 673 2 512,
   pushAt 674 2 256,
   pushAt 675 2 3353,
   opAt 676 .JUMP]

/-- Instructions 1389..1389, pc 1958..1958. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 677 .JUMPDEST]

/-- Instructions 1438..1395, pc 1829..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 678 .JUMPDEST,
   pushAt 679 1 1,
   opAt 680 .SHR,
   opAt 681 (.Dup ⟨0, by decide⟩),
   pushAt 682 2 951,
   opAt 683 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
