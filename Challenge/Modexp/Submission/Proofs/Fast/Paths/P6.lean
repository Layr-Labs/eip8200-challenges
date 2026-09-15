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
  [opAt 694 .POP,
   opAt 695 .POP,
   pushAt 696 1 1,
   opAt 697 .ADD,
   pushAt 698 2 950,
   opAt 699 .JUMP]

/-- Instructions 1402..1414, pc 1977..2002. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 700 .JUMPDEST,
   opAt 701 .POP,
   pushAt 702 1 1,
   opAt 703 (.Dup ⟨1, by decide⟩),
   pushAt 704 2 736,
   opAt 705 .ADD,
   opAt 706 .MSTORE,
   pushAt 707 2 1049,
   pushAt 708 2 256,
   pushAt 709 2 768,
   pushAt 710 2 256,
   pushAt 711 2 3209,
   opAt 712 .JUMP]

/-- Instructions 1463..1470, pc 2003..2012. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 715 .JUMPDEST,
   opAt 716 (.Dup ⟨4, by decide⟩),
   opAt 717 (.Dup ⟨0, by decide⟩),
   opAt 718 (.Dup ⟨2, by decide⟩),
   pushAt 719 2 256,
   opAt 720 .ADD,
   opAt 721 .SUB,
   opAt 722 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 723 .JUMPDEST,
   opAt 724 .POP,
   pushAt 725 2 553,
   opAt 726 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 715..717, pc 1053..1056: the six-word bail.  The wide-modulus
fallback re-reads the header itself, so the live words are no longer dropped and the
block jumps straight to the fallback entry at pc 236. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 727 .JUMPDEST,
   pushAt 728 1 238,
   opAt 729 .JUMP]

/-- Instructions 1408..1361, pc 2038..2039. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 730 .JUMPDEST,
   pushAt 731 2 256]

/-- Instructions 1362..1368, pc 2042..2052. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 732 .JUMPDEST,
   pushAt 733 2 1084,
   opAt 734 (.Dup ⟨2, by decide⟩),
   opAt 735 (.Dup ⟨0, by decide⟩),
   opAt 736 (.Dup ⟨0, by decide⟩),
   pushAt 737 2 1097,
   opAt 738 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
