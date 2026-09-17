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
  [pushAt 606 2 2044,
   opAt 607 .JUMP]

/-- Instructions 1216..1352, pc 1795..1803. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 608 .JUMPDEST,
   opAt 609 (.Dup ⟨1, by decide⟩),
   opAt 610 (.Dup ⟨1, by decide⟩),
   opAt 611 .EQ,
   pushAt 612 2 931,
   opAt 613 .JUMPI]

/-- Instructions 1353..1358, pc 1804..1819. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 614 2 888,
   pushAt 615 2 256,
   pushAt 616 2 1280,
   pushAt 617 2 256,
   pushAt 618 2 3209,
   opAt 619 .JUMP]

/-- Instructions 1359..1379, pc 1820..1806. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 620 .JUMPDEST,
   opAt 621 (.Dup ⟨0, by decide⟩),
   opAt 622 (.Dup ⟨2, by decide⟩),
   opAt 623 .SUB,
   pushAt 624 1 5,
   opAt 625 .SHL,
   opAt 626 (.Dup ⟨5, by decide⟩),
   opAt 627 .SUB,
   pushAt 628 1 96,
   opAt 629 .ADD,
   opAt 630 .CALLDATALOAD,
   opAt 631 (.Dup ⟨3, by decide⟩),
   pushAt 632 2 736,
   opAt 633 .ADD,
   opAt 634 .MSTORE,
   pushAt 635 2 923,
   pushAt 636 2 256,
   pushAt 637 2 768,
   pushAt 638 2 256,
   pushAt 639 2 1097,
   opAt 640 .JUMP]

/-- Instructions 1332..1384, pc 1728..1814. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 641 .JUMPDEST,
   pushAt 642 1 1,
   opAt 643 .ADD,
   pushAt 644 2 864,
   opAt 645 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
