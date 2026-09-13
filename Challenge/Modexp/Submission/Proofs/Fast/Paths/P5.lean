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
  [opAt 714 .JUMPDEST,
   opAt 715 .POP,
   opAt 716 .POP,
   pushAt 717 2 2675,
   pushAt 718 2 512,
   pushAt 719 2 1536,
   pushAt 720 2 256,
   pushAt 721 2 3536,
   opAt 722 .JUMP]

/-- Instructions 1402..1360, pc 1896..1904. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 723 .JUMPDEST,
   opAt 724 (.Dup ⟨4, by decide⟩),
   opAt 725 (.Dup ⟨1, by decide⟩),
   opAt 726 .EQ,
   pushAt 727 2 1132,
   opAt 728 .JUMPI]

/-- Instructions 1409..1416, pc 1905..1914. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 729 2 1691,
   opAt 730 .JUMP]

/-- Instructions 1417..1423, pc 1916..1932. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 731 .JUMPDEST,
   pushAt 732 2 1088,
   pushAt 733 2 256,
   opAt 734 (.Dup ⟨0, by decide⟩),
   pushAt 735 2 256,
   pushAt 736 2 3536,
   opAt 737 .JUMP]

/-- Instructions 1424..1430, pc 1933..1941. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 738 .JUMPDEST,
   opAt 739 (.Dup ⟨1, by decide⟩),
   opAt 740 (.Dup ⟨1, by decide⟩),
   opAt 741 .AND,
   opAt 742 .ISZERO,
   pushAt 743 2 1114,
   opAt 744 .JUMPI]

/-- Instructions 1431..1388, pc 1942..1957. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 745 2 1113,
   pushAt 746 2 256,
   pushAt 747 2 512,
   pushAt 748 2 256,
   pushAt 749 2 3536,
   opAt 750 .JUMP]

/-- Instructions 1389..1389, pc 1958..1958. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 751 .JUMPDEST]

/-- Instructions 1438..1395, pc 1829..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 752 .JUMPDEST,
   pushAt 753 1 1,
   opAt 754 .SHR,
   opAt 755 (.Dup ⟨0, by decide⟩),
   pushAt 756 2 1073,
   opAt 757 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
