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
  [opAt 690 .POP,
   opAt 691 .POP,
   pushAt 692 1 1,
   opAt 693 .ADD,
   pushAt 694 2 950,
   opAt 695 .JUMP]

/-- Instructions 1402..1414, pc 1977..2002. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 696 .JUMPDEST,
   opAt 697 .POP,
   pushAt 698 1 1,
   opAt 699 (.Dup ⟨1, by decide⟩),
   pushAt 700 2 736,
   opAt 701 .ADD,
   opAt 702 .MSTORE,
   pushAt 703 2 1049,
   pushAt 704 2 256,
   pushAt 705 2 768,
   pushAt 706 2 256,
   pushAt 707 2 3209,
   opAt 708 .JUMP]

/-- Instructions 1463..1470, pc 2003..2012. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 711 .JUMPDEST,
   opAt 712 (.Dup ⟨4, by decide⟩),
   opAt 713 (.Dup ⟨0, by decide⟩),
   opAt 714 (.Dup ⟨2, by decide⟩),
   pushAt 715 2 256,
   opAt 716 .ADD,
   opAt 717 .SUB,
   opAt 718 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 719 .JUMPDEST,
   opAt 720 .POP,
   pushAt 721 2 553,
   opAt 722 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 715..717, pc 1053..1056: the six-word bail.  The wide-modulus
fallback re-reads the header itself, so the live words are no longer dropped and the
block jumps straight to the fallback entry at pc 236. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 723 .JUMPDEST,
   pushAt 724 1 238,
   opAt 725 .JUMP]

/-- Instructions 1408..1361, pc 2038..2039. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 726 .JUMPDEST,
   pushAt 727 2 256]

/-- Instructions 1362..1368, pc 2042..2052. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 728 .JUMPDEST,
   pushAt 729 2 1084,
   opAt 730 (.Dup ⟨2, by decide⟩),
   opAt 731 (.Dup ⟨0, by decide⟩),
   opAt 732 (.Dup ⟨0, by decide⟩),
   pushAt 733 2 1097,
   opAt 734 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
