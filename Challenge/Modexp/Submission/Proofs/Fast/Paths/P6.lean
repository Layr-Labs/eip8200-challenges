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
  [opAt 763 .POP,
   opAt 764 .POP,
   pushAt 765 1 1,
   opAt 766 .ADD,
   pushAt 767 2 1065,
   opAt 768 .JUMP]

/-- Instructions 1402..1414, pc 1977..2002. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 769 .JUMPDEST,
   opAt 770 .POP,
   pushAt 771 1 1,
   opAt 772 (.Dup ⟨1, by decide⟩),
   pushAt 773 2 736,
   opAt 774 .ADD,
   opAt 775 .MSTORE,
   pushAt 776 2 1164,
   pushAt 777 2 256,
   pushAt 778 2 768,
   pushAt 779 2 256,
   pushAt 780 2 3552,
   opAt 781 .JUMP]

/-- Instructions 1463..1470, pc 2003..2012. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 784 .JUMPDEST,
   opAt 785 (.Dup ⟨4, by decide⟩),
   opAt 786 (.Dup ⟨0, by decide⟩),
   opAt 787 (.Dup ⟨2, by decide⟩),
   pushAt 788 2 256,
   opAt 789 .ADD,
   opAt 790 .SUB,
   opAt 791 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 792 .JUMPDEST,
   opAt 793 .POP,
   pushAt 794 2 655,
   opAt 795 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1481..1489, pc 1897..2037. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 796 .JUMPDEST,
   opAt 797 .POP,
   opAt 798 .POP,
   opAt 799 .POP,
   opAt 800 .POP,
   opAt 801 .POP,
   opAt 802 .POP,
   pushAt 803 2 655,
   opAt 804 .JUMP]

/-- Instructions 1408..1361, pc 2038..2039. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 805 .JUMPDEST,
   pushAt 806 2 256]

/-- Instructions 1362..1368, pc 2042..2052. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 807 .JUMPDEST,
   pushAt 808 2 1206,
   opAt 809 (.Dup ⟨2, by decide⟩),
   opAt 810 (.Dup ⟨0, by decide⟩),
   opAt 811 (.Dup ⟨0, by decide⟩),
   pushAt 812 2 1491,
   opAt 813 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
