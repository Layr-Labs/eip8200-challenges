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
  [pushAt 671 2 2430,
   opAt 672 .JUMP]

/-- Instructions 1216..1352, pc 1795..1803. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 673 .JUMPDEST,
   opAt 674 (.Dup ⟨1, by decide⟩),
   opAt 675 (.Dup ⟨1, by decide⟩),
   opAt 676 .EQ,
   pushAt 677 2 1029,
   opAt 678 .JUMPI]

/-- Instructions 1353..1358, pc 1804..1819. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 679 2 986,
   pushAt 680 2 256,
   pushAt 681 2 1280,
   pushAt 682 2 256,
   pushAt 683 2 3546,
   opAt 684 .JUMP]

/-- Instructions 1359..1379, pc 1820..1806. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 685 .JUMPDEST,
   opAt 686 (.Dup ⟨0, by decide⟩),
   opAt 687 (.Dup ⟨2, by decide⟩),
   opAt 688 .SUB,
   pushAt 689 1 5,
   opAt 690 .SHL,
   opAt 691 (.Dup ⟨5, by decide⟩),
   opAt 692 .SUB,
   pushAt 693 1 96,
   opAt 694 .ADD,
   opAt 695 .CALLDATALOAD,
   opAt 696 (.Dup ⟨3, by decide⟩),
   pushAt 697 2 736,
   opAt 698 .ADD,
   opAt 699 .MSTORE,
   pushAt 700 2 1021,
   pushAt 701 2 256,
   pushAt 702 2 768,
   pushAt 703 2 256,
   pushAt 704 2 1475,
   opAt 705 .JUMP]

/-- Instructions 1332..1384, pc 1728..1814. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 706 .JUMPDEST,
   pushAt 707 1 1,
   opAt 708 .ADD,
   pushAt 709 2 962,
   opAt 710 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
