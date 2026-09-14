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
  [opAt 757 .POP,
   opAt 758 .POP,
   pushAt 759 1 1,
   opAt 760 .ADD,
   pushAt 761 2 1049,
   opAt 762 .JUMP]

/-- Instructions 1402..1414, pc 1977..2002. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 763 .JUMPDEST,
   opAt 764 .POP,
   pushAt 765 1 1,
   opAt 766 (.Dup ⟨1, by decide⟩),
   pushAt 767 2 736,
   opAt 768 .ADD,
   opAt 769 .MSTORE,
   pushAt 770 2 1148,
   pushAt 771 2 256,
   pushAt 772 2 768,
   pushAt 773 2 256,
   pushAt 774 2 3550,
   opAt 775 .JUMP]

/-- Instructions 1463..1470, pc 2003..2012. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 778 .JUMPDEST,
   opAt 779 (.Dup ⟨4, by decide⟩),
   opAt 780 (.Dup ⟨0, by decide⟩),
   opAt 781 (.Dup ⟨2, by decide⟩),
   pushAt 782 2 256,
   opAt 783 .ADD,
   opAt 784 .SUB,
   opAt 785 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 786 .JUMPDEST,
   opAt 787 .POP,
   pushAt 788 2 648,
   opAt 789 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1481..1489, pc 1897..2037. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 790 .JUMPDEST,
   opAt 791 .POP,
   opAt 792 .POP,
   opAt 793 .POP,
   opAt 794 .POP,
   opAt 795 .POP,
   opAt 796 .POP,
   pushAt 797 2 648,
   opAt 798 .JUMP]

/-- Instructions 1408..1361, pc 2038..2039. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 799 .JUMPDEST,
   pushAt 800 2 256]

/-- Instructions 1362..1368, pc 2042..2052. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 801 .JUMPDEST,
   pushAt 802 2 1190,
   opAt 803 (.Dup ⟨2, by decide⟩),
   opAt 804 (.Dup ⟨0, by decide⟩),
   opAt 805 (.Dup ⟨0, by decide⟩),
   pushAt 806 2 1475,
   opAt 807 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
