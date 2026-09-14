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
  [opAt 713 .JUMPDEST,
   opAt 714 .POP,
   opAt 715 .POP,
   pushAt 716 2 2637,
   pushAt 717 2 512,
   pushAt 718 2 1536,
   pushAt 719 2 256,
   pushAt 720 2 3550,
   opAt 721 .JUMP]

/-- Instructions 1402..1360, pc 1896..1904. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 722 .JUMPDEST,
   opAt 723 (.Dup ⟨4, by decide⟩),
   opAt 724 (.Dup ⟨1, by decide⟩),
   opAt 725 .EQ,
   pushAt 726 2 1120,
   opAt 727 .JUMPI]

/-- Instructions 1409..1416, pc 1905..1914. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 728 2 1679,
   opAt 729 .JUMP]

/-- Instructions 1417..1423, pc 1916..1932. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 730 .JUMPDEST,
   pushAt 731 2 1076,
   pushAt 732 2 256,
   opAt 733 (.Dup ⟨0, by decide⟩),
   pushAt 734 2 256,
   pushAt 735 2 3550,
   opAt 736 .JUMP]

/-- Instructions 1424..1430, pc 1933..1941. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 737 .JUMPDEST,
   opAt 738 (.Dup ⟨1, by decide⟩),
   opAt 739 (.Dup ⟨1, by decide⟩),
   opAt 740 .AND,
   opAt 741 .ISZERO,
   pushAt 742 2 1102,
   opAt 743 .JUMPI]

/-- Instructions 1431..1388, pc 1942..1957. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 744 2 1101,
   pushAt 745 2 256,
   pushAt 746 2 512,
   pushAt 747 2 256,
   pushAt 748 2 3550,
   opAt 749 .JUMP]

/-- Instructions 1389..1389, pc 1958..1958. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 750 .JUMPDEST]

/-- Instructions 1438..1395, pc 1829..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 751 .JUMPDEST,
   pushAt 752 1 1,
   opAt 753 .SHR,
   opAt 754 (.Dup ⟨0, by decide⟩),
   pushAt 755 2 1061,
   opAt 756 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
