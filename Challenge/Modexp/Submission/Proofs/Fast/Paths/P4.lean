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
  [pushAt 672 2 2430,
   opAt 673 .JUMP]

/-- Instructions 1216..1352, pc 1795..1803. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 674 .JUMPDEST,
   opAt 675 (.Dup ⟨1, by decide⟩),
   opAt 676 (.Dup ⟨1, by decide⟩),
   opAt 677 .EQ,
   pushAt 678 2 1030,
   opAt 679 .JUMPI]

/-- Instructions 1353..1358, pc 1804..1819. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 680 2 987,
   pushAt 681 2 256,
   pushAt 682 2 1280,
   pushAt 683 2 256,
   pushAt 684 2 3550,
   opAt 685 .JUMP]

/-- Instructions 1359..1379, pc 1820..1806. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 686 .JUMPDEST,
   opAt 687 (.Dup ⟨0, by decide⟩),
   opAt 688 (.Dup ⟨2, by decide⟩),
   opAt 689 .SUB,
   pushAt 690 1 5,
   opAt 691 .SHL,
   opAt 692 (.Dup ⟨5, by decide⟩),
   opAt 693 .SUB,
   pushAt 694 1 96,
   opAt 695 .ADD,
   opAt 696 .CALLDATALOAD,
   opAt 697 (.Dup ⟨3, by decide⟩),
   pushAt 698 2 736,
   opAt 699 .ADD,
   opAt 700 .MSTORE,
   pushAt 701 2 1022,
   pushAt 702 2 256,
   pushAt 703 2 768,
   pushAt 704 2 256,
   pushAt 705 2 1475,
   opAt 706 .JUMP]

/-- Instructions 1332..1384, pc 1728..1814. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 707 .JUMPDEST,
   pushAt 708 1 1,
   opAt 709 .ADD,
   pushAt 710 2 963,
   opAt 711 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
