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
  [opAt 755 .POP,
   opAt 756 .POP,
   pushAt 757 1 1,
   opAt 758 .ADD,
   pushAt 759 2 1048,
   opAt 760 .JUMP]

/-- Instructions 1402..1414, pc 1977..2002. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 761 .JUMPDEST,
   opAt 762 .POP,
   pushAt 763 1 1,
   opAt 764 (.Dup ⟨1, by decide⟩),
   pushAt 765 2 736,
   opAt 766 .ADD,
   opAt 767 .MSTORE,
   pushAt 768 2 1147,
   pushAt 769 2 256,
   pushAt 770 2 768,
   pushAt 771 2 256,
   pushAt 772 2 3549,
   opAt 773 .JUMP]

/-- Instructions 1463..1470, pc 2003..2012. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 776 .JUMPDEST,
   opAt 777 (.Dup ⟨4, by decide⟩),
   opAt 778 (.Dup ⟨0, by decide⟩),
   opAt 779 (.Dup ⟨2, by decide⟩),
   pushAt 780 2 256,
   opAt 781 .ADD,
   opAt 782 .SUB,
   opAt 783 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 784 .JUMPDEST,
   opAt 785 .POP,
   pushAt 786 2 647,
   opAt 787 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1481..1489, pc 1897..2037. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 788 .JUMPDEST,
   opAt 789 .POP,
   opAt 790 .POP,
   opAt 791 .POP,
   opAt 792 .POP,
   opAt 793 .POP,
   opAt 794 .POP,
   pushAt 795 2 647,
   opAt 796 .JUMP]

/-- Instructions 1408..1361, pc 2038..2039. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 797 .JUMPDEST,
   pushAt 798 2 256]

/-- Instructions 1362..1368, pc 2042..2052. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 799 .JUMPDEST,
   pushAt 800 2 1189,
   opAt 801 (.Dup ⟨2, by decide⟩),
   opAt 802 (.Dup ⟨0, by decide⟩),
   opAt 803 (.Dup ⟨0, by decide⟩),
   pushAt 804 2 1474,
   opAt 805 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
