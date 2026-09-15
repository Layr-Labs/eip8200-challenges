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
  [pushAt 610 2 2044,
   opAt 611 .JUMP]

/-- Instructions 1216..1352, pc 1795..1803. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 612 .JUMPDEST,
   opAt 613 (.Dup ⟨1, by decide⟩),
   opAt 614 (.Dup ⟨1, by decide⟩),
   opAt 615 .EQ,
   pushAt 616 2 931,
   opAt 617 .JUMPI]

/-- Instructions 1353..1358, pc 1804..1819. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 618 2 888,
   pushAt 619 2 256,
   pushAt 620 2 1280,
   pushAt 621 2 256,
   pushAt 622 2 3209,
   opAt 623 .JUMP]

/-- Instructions 1359..1379, pc 1820..1806. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 624 .JUMPDEST,
   opAt 625 (.Dup ⟨0, by decide⟩),
   opAt 626 (.Dup ⟨2, by decide⟩),
   opAt 627 .SUB,
   pushAt 628 1 5,
   opAt 629 .SHL,
   opAt 630 (.Dup ⟨5, by decide⟩),
   opAt 631 .SUB,
   pushAt 632 1 96,
   opAt 633 .ADD,
   opAt 634 .CALLDATALOAD,
   opAt 635 (.Dup ⟨3, by decide⟩),
   pushAt 636 2 736,
   opAt 637 .ADD,
   opAt 638 .MSTORE,
   pushAt 639 2 923,
   pushAt 640 2 256,
   pushAt 641 2 768,
   pushAt 642 2 256,
   pushAt 643 2 1097,
   opAt 644 .JUMP]

/-- Instructions 1332..1384, pc 1728..1814. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 645 .JUMPDEST,
   pushAt 646 1 1,
   opAt 647 .ADD,
   pushAt 648 2 864,
   opAt 649 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
