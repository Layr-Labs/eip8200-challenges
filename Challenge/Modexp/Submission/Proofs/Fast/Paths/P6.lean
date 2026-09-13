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
  [opAt 758 .POP,
   opAt 759 .POP,
   pushAt 760 1 1,
   opAt 761 .ADD,
   pushAt 762 2 1065,
   opAt 763 .JUMP]

/-- Instructions 1402..1414, pc 1977..2002. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 764 .JUMPDEST,
   opAt 765 .POP,
   pushAt 766 1 1,
   opAt 767 (.Dup ⟨1, by decide⟩),
   pushAt 768 2 736,
   opAt 769 .ADD,
   opAt 770 .MSTORE,
   pushAt 771 2 1164,
   pushAt 772 2 256,
   pushAt 773 2 768,
   pushAt 774 2 256,
   pushAt 775 2 3552,
   opAt 776 .JUMP]

/-- Instructions 1463..1470, pc 2003..2012. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 779 .JUMPDEST,
   opAt 780 (.Dup ⟨4, by decide⟩),
   opAt 781 (.Dup ⟨0, by decide⟩),
   opAt 782 (.Dup ⟨2, by decide⟩),
   pushAt 783 2 256,
   opAt 784 .ADD,
   opAt 785 .SUB,
   opAt 786 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 787 .JUMPDEST,
   opAt 788 .POP,
   pushAt 789 2 655,
   opAt 790 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1481..1489, pc 1897..2037. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 791 .JUMPDEST,
   opAt 792 .POP,
   opAt 793 .POP,
   opAt 794 .POP,
   opAt 795 .POP,
   opAt 796 .POP,
   opAt 797 .POP,
   pushAt 798 2 655,
   opAt 799 .JUMP]

/-- Instructions 1408..1361, pc 2038..2039. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 800 .JUMPDEST,
   pushAt 801 2 256]

/-- Instructions 1362..1368, pc 2042..2052. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 802 .JUMPDEST,
   pushAt 803 2 1206,
   opAt 804 (.Dup ⟨2, by decide⟩),
   opAt 805 (.Dup ⟨0, by decide⟩),
   opAt 806 (.Dup ⟨0, by decide⟩),
   pushAt 807 2 1491,
   opAt 808 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
