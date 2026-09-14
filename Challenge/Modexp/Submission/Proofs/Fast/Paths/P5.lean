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
  [opAt 711 .JUMPDEST,
   opAt 712 .POP,
   opAt 713 .POP,
   pushAt 714 2 2637,
   pushAt 715 2 512,
   pushAt 716 2 1536,
   pushAt 717 2 256,
   pushAt 718 2 3550,
   opAt 719 .JUMP]

/-- Instructions 1402..1360, pc 1896..1904. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 720 .JUMPDEST,
   opAt 721 (.Dup ⟨4, by decide⟩),
   opAt 722 (.Dup ⟨1, by decide⟩),
   opAt 723 .EQ,
   pushAt 724 2 1119,
   opAt 725 .JUMPI]

/-- Instructions 1409..1416, pc 1905..1914. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 726 2 1678,
   opAt 727 .JUMP]

/-- Instructions 1417..1423, pc 1916..1932. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 728 .JUMPDEST,
   pushAt 729 2 1075,
   pushAt 730 2 256,
   opAt 731 (.Dup ⟨0, by decide⟩),
   pushAt 732 2 256,
   pushAt 733 2 3550,
   opAt 734 .JUMP]

/-- Instructions 1424..1430, pc 1933..1941. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 735 .JUMPDEST,
   opAt 736 (.Dup ⟨1, by decide⟩),
   opAt 737 (.Dup ⟨1, by decide⟩),
   opAt 738 .AND,
   opAt 739 .ISZERO,
   pushAt 740 2 1101,
   opAt 741 .JUMPI]

/-- Instructions 1431..1388, pc 1942..1957. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 742 2 1100,
   pushAt 743 2 256,
   pushAt 744 2 512,
   pushAt 745 2 256,
   pushAt 746 2 3550,
   opAt 747 .JUMP]

/-- Instructions 1389..1389, pc 1958..1958. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 748 .JUMPDEST]

/-- Instructions 1438..1395, pc 1829..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 749 .JUMPDEST,
   pushAt 750 1 1,
   opAt 751 .SHR,
   opAt 752 (.Dup ⟨0, by decide⟩),
   pushAt 753 2 1060,
   opAt 754 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
