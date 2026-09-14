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
  [opAt 682 .POP,
   opAt 683 .POP,
   pushAt 684 1 1,
   opAt 685 .ADD,
   pushAt 686 2 937,
   opAt 687 .JUMP]

/-- Instructions 1402..1414, pc 1977..2002. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 688 .JUMPDEST,
   opAt 689 .POP,
   pushAt 690 1 1,
   opAt 691 (.Dup ⟨1, by decide⟩),
   pushAt 692 2 736,
   opAt 693 .ADD,
   opAt 694 .MSTORE,
   pushAt 695 2 1037,
   pushAt 696 2 256,
   pushAt 697 2 768,
   pushAt 698 2 256,
   pushAt 699 2 3349,
   opAt 700 .JUMP]

/-- Instructions 1463..1470, pc 2003..2012. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 703 .JUMPDEST,
   opAt 704 (.Dup ⟨4, by decide⟩),
   opAt 705 (.Dup ⟨0, by decide⟩),
   opAt 706 (.Dup ⟨2, by decide⟩),
   pushAt 707 2 256,
   opAt 708 .ADD,
   opAt 709 .SUB,
   opAt 710 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 711 .JUMPDEST,
   opAt 712 .POP,
   pushAt 713 2 551,
   opAt 714 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 715..717, pc 1053..1056: the six-word bail.  The wide-modulus
fallback re-reads the header itself, so the live words are no longer dropped and the
block jumps straight to the fallback entry at pc 236. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 715 .JUMPDEST,
   pushAt 716 1 236,
   opAt 717 .JUMP]

/-- Instructions 1408..1361, pc 2038..2039. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 718 .JUMPDEST,
   pushAt 719 2 256]

/-- Instructions 1362..1368, pc 2042..2052. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 720 .JUMPDEST,
   pushAt 721 2 1072,
   opAt 722 (.Dup ⟨2, by decide⟩),
   opAt 723 (.Dup ⟨0, by decide⟩),
   opAt 724 (.Dup ⟨0, by decide⟩),
   pushAt 725 2 1357,
   opAt 726 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
