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
  [opAt 712 .JUMPDEST,
   opAt 713 .POP,
   opAt 714 .POP,
   pushAt 715 2 2638,
   pushAt 716 2 512,
   pushAt 717 2 1536,
   pushAt 718 2 256,
   pushAt 719 2 3550,
   opAt 720 .JUMP]

/-- Instructions 1402..1360, pc 1896..1904. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 721 .JUMPDEST,
   opAt 722 (.Dup ⟨4, by decide⟩),
   opAt 723 (.Dup ⟨1, by decide⟩),
   opAt 724 .EQ,
   pushAt 725 2 1120,
   opAt 726 .JUMPI]

/-- Instructions 1409..1416, pc 1905..1914. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 727 2 1679,
   opAt 728 .JUMP]

/-- Instructions 1417..1423, pc 1916..1932. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 729 .JUMPDEST,
   pushAt 730 2 1076,
   pushAt 731 2 256,
   opAt 732 (.Dup ⟨0, by decide⟩),
   pushAt 733 2 256,
   pushAt 734 2 3550,
   opAt 735 .JUMP]

/-- Instructions 1424..1430, pc 1933..1941. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 736 .JUMPDEST,
   opAt 737 (.Dup ⟨1, by decide⟩),
   opAt 738 (.Dup ⟨1, by decide⟩),
   opAt 739 .AND,
   opAt 740 .ISZERO,
   pushAt 741 2 1102,
   opAt 742 .JUMPI]

/-- Instructions 1431..1388, pc 1942..1957. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 743 2 1101,
   pushAt 744 2 256,
   pushAt 745 2 512,
   pushAt 746 2 256,
   pushAt 747 2 3550,
   opAt 748 .JUMP]

/-- Instructions 1389..1389, pc 1958..1958. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 749 .JUMPDEST]

/-- Instructions 1438..1395, pc 1829..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 750 .JUMPDEST,
   pushAt 751 1 1,
   opAt 752 .SHR,
   opAt 753 (.Dup ⟨0, by decide⟩),
   pushAt 754 2 1061,
   opAt 755 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
