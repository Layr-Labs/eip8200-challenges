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
  [pushAt 679 2 2473,
   opAt 680 .JUMP]

/-- Instructions 1216..1352, pc 1795..1803. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 681 .JUMPDEST,
   opAt 682 (.Dup ⟨1, by decide⟩),
   opAt 683 (.Dup ⟨1, by decide⟩),
   opAt 684 .EQ,
   pushAt 685 2 1046,
   opAt 686 .JUMPI]

/-- Instructions 1353..1358, pc 1804..1819. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 687 2 1003,
   pushAt 688 2 256,
   pushAt 689 2 1280,
   pushAt 690 2 256,
   pushAt 691 2 3552,
   opAt 692 .JUMP]

/-- Instructions 1359..1379, pc 1820..1806. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 693 .JUMPDEST,
   opAt 694 (.Dup ⟨0, by decide⟩),
   opAt 695 (.Dup ⟨2, by decide⟩),
   opAt 696 .SUB,
   pushAt 697 1 5,
   opAt 698 .SHL,
   opAt 699 (.Dup ⟨5, by decide⟩),
   opAt 700 .SUB,
   pushAt 701 1 96,
   opAt 702 .ADD,
   opAt 703 .CALLDATALOAD,
   opAt 704 (.Dup ⟨3, by decide⟩),
   pushAt 705 2 736,
   opAt 706 .ADD,
   opAt 707 .MSTORE,
   pushAt 708 2 1038,
   pushAt 709 2 256,
   pushAt 710 2 768,
   pushAt 711 2 256,
   pushAt 712 2 1491,
   opAt 713 .JUMP]

/-- Instructions 1332..1384, pc 1728..1814. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 714 .JUMPDEST,
   pushAt 715 1 1,
   opAt 716 .ADD,
   pushAt 717 2 979,
   opAt 718 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
