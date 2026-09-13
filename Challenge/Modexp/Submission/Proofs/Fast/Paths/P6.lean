import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 6 (instructions 1396..1368). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1396..1323, pc 1968..1976. -/
def blk1314 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 756 .POP,
   opAt 757 .POP,
   pushAt 758 1 1,
   opAt 759 .ADD,
   pushAt 760 2 1049,
   opAt 761 .JUMP]

/-- Instructions 1402..1414, pc 1977..2002. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 762 .JUMPDEST,
   opAt 763 .POP,
   pushAt 764 1 1,
   opAt 765 (.Dup ⟨1, by decide⟩),
   pushAt 766 2 736,
   opAt 767 .ADD,
   opAt 768 .MSTORE,
   pushAt 769 2 1148,
   pushAt 770 2 256,
   pushAt 771 2 768,
   pushAt 772 2 256,
   pushAt 773 2 3552,
   opAt 774 .JUMP]

/-- Instructions 1463..1470, pc 2003..2012. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 777 .JUMPDEST,
   opAt 778 (.Dup ⟨4, by decide⟩),
   opAt 779 (.Dup ⟨0, by decide⟩),
   opAt 780 (.Dup ⟨2, by decide⟩),
   pushAt 781 2 256,
   opAt 782 .ADD,
   opAt 783 .SUB,
   opAt 784 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 785 .JUMPDEST,
   opAt 786 .POP,
   pushAt 787 2 647,
   opAt 788 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1481..1489, pc 1897..2037. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 789 .JUMPDEST,
   opAt 790 .POP,
   opAt 791 .POP,
   opAt 792 .POP,
   opAt 793 .POP,
   opAt 794 .POP,
   opAt 795 .POP,
   pushAt 796 2 647,
   opAt 797 .JUMP]

/-- Instructions 1408..1361, pc 2038..2039. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 798 .JUMPDEST,
   pushAt 799 2 256]

/-- Instructions 1362..1368, pc 2042..2052. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 800 .JUMPDEST,
   pushAt 801 2 1190,
   opAt 802 (.Dup ⟨2, by decide⟩),
   opAt 803 (.Dup ⟨0, by decide⟩),
   opAt 804 (.Dup ⟨0, by decide⟩),
   pushAt 805 2 1475,
   opAt 806 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
