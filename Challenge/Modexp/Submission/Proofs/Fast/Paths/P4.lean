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
  [pushAt 600 2 2305,
   opAt 601 .JUMP]

/-- Instructions 1216..1352, pc 1795..1803. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 602 .JUMPDEST,
   opAt 603 (.Dup ⟨1, by decide⟩),
   opAt 604 (.Dup ⟨1, by decide⟩),
   opAt 605 .EQ,
   pushAt 606 2 920,
   opAt 607 .JUMPI]

/-- Instructions 1353..1358, pc 1804..1819. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 608 2 877,
   pushAt 609 2 256,
   pushAt 610 2 1280,
   pushAt 611 2 256,
   pushAt 612 2 3353,
   opAt 613 .JUMP]

/-- Instructions 1359..1379, pc 1820..1806. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 614 .JUMPDEST,
   opAt 615 (.Dup ⟨0, by decide⟩),
   opAt 616 (.Dup ⟨2, by decide⟩),
   opAt 617 .SUB,
   pushAt 618 1 5,
   opAt 619 .SHL,
   opAt 620 (.Dup ⟨5, by decide⟩),
   opAt 621 .SUB,
   pushAt 622 1 96,
   opAt 623 .ADD,
   opAt 624 .CALLDATALOAD,
   opAt 625 (.Dup ⟨3, by decide⟩),
   pushAt 626 2 736,
   opAt 627 .ADD,
   opAt 628 .MSTORE,
   pushAt 629 2 912,
   pushAt 630 2 256,
   pushAt 631 2 768,
   pushAt 632 2 256,
   pushAt 633 2 1358,
   opAt 634 .JUMP]

/-- Instructions 1332..1384, pc 1728..1814. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 635 .JUMPDEST,
   pushAt 636 1 1,
   opAt 637 .ADD,
   pushAt 638 2 853,
   opAt 639 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
