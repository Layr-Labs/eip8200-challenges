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
  [opAt 684 .POP,
   opAt 685 .POP,
   pushAt 686 1 1,
   opAt 687 .ADD,
   pushAt 688 2 939,
   opAt 689 .JUMP]

/-- Instructions 1402..1414, pc 1977..2002. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 690 .JUMPDEST,
   opAt 691 .POP,
   pushAt 692 1 1,
   opAt 693 (.Dup ⟨1, by decide⟩),
   pushAt 694 2 736,
   opAt 695 .ADD,
   opAt 696 .MSTORE,
   pushAt 697 2 1038,
   pushAt 698 2 256,
   pushAt 699 2 768,
   pushAt 700 2 256,
   pushAt 701 2 3353,
   opAt 702 .JUMP]

/-- Instructions 1463..1470, pc 2003..2012. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 705 .JUMPDEST,
   opAt 706 (.Dup ⟨4, by decide⟩),
   opAt 707 (.Dup ⟨0, by decide⟩),
   opAt 708 (.Dup ⟨2, by decide⟩),
   pushAt 709 2 256,
   opAt 710 .ADD,
   opAt 711 .SUB,
   opAt 712 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 713 .JUMPDEST,
   opAt 714 .POP,
   pushAt 715 2 553,
   opAt 716 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 715..717, pc 1053..1056: the six-word bail.  The wide-modulus
fallback re-reads the header itself, so the live words are no longer dropped and the
block jumps straight to the fallback entry at pc 236. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 717 .JUMPDEST,
   pushAt 718 1 238,
   opAt 719 .JUMP]

/-- Instructions 1408..1361, pc 2038..2039. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 720 .JUMPDEST,
   pushAt 721 2 256]

/-- Instructions 1362..1368, pc 2042..2052. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 722 .JUMPDEST,
   pushAt 723 2 1073,
   opAt 724 (.Dup ⟨2, by decide⟩),
   opAt 725 (.Dup ⟨0, by decide⟩),
   opAt 726 (.Dup ⟨0, by decide⟩),
   pushAt 727 2 1358,
   opAt 728 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
