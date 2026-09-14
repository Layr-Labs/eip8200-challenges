import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 4 (instructions 1325..1384). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1325..1326, pc 1766..1769: jump to the appended full-base
dispatcher. The remaining decoded instructions through index 1215 are
unreachable padding, preserving the old loop head at index 1216 / pc 1795. -/
def blk1195 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 598 2 2301,
   opAt 599 .JUMP]

/-- Instructions 1216..1352, pc 1795..1803. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 600 .JUMPDEST,
   opAt 601 (.Dup ⟨1, by decide⟩),
   opAt 602 (.Dup ⟨1, by decide⟩),
   opAt 603 .EQ,
   pushAt 604 2 918,
   opAt 605 .JUMPI]

/-- Instructions 1353..1358, pc 1804..1819. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 606 2 875,
   pushAt 607 2 256,
   pushAt 608 2 1280,
   pushAt 609 2 256,
   pushAt 610 2 3349,
   opAt 611 .JUMP]

/-- Instructions 1359..1379, pc 1820..1806. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 612 .JUMPDEST,
   opAt 613 (.Dup ⟨0, by decide⟩),
   opAt 614 (.Dup ⟨2, by decide⟩),
   opAt 615 .SUB,
   pushAt 616 1 5,
   opAt 617 .SHL,
   opAt 618 (.Dup ⟨5, by decide⟩),
   opAt 619 .SUB,
   pushAt 620 1 96,
   opAt 621 .ADD,
   opAt 622 .CALLDATALOAD,
   opAt 623 (.Dup ⟨3, by decide⟩),
   pushAt 624 2 736,
   opAt 625 .ADD,
   opAt 626 .MSTORE,
   pushAt 627 2 910,
   pushAt 628 2 256,
   pushAt 629 2 768,
   pushAt 630 2 256,
   pushAt 631 2 1357,
   opAt 632 .JUMP]

/-- Instructions 1332..1384, pc 1728..1814. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 633 .JUMPDEST,
   pushAt 634 1 1,
   opAt 635 .ADD,
   pushAt 636 2 851,
   opAt 637 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
