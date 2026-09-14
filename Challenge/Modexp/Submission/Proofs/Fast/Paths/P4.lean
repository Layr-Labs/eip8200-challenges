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
  [pushAt 673 2 2429,
   opAt 674 .JUMP]

/-- Instructions 1216..1352, pc 1795..1803. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 675 .JUMPDEST,
   opAt 676 (.Dup ⟨1, by decide⟩),
   opAt 677 (.Dup ⟨1, by decide⟩),
   opAt 678 .EQ,
   pushAt 679 2 1030,
   opAt 680 .JUMPI]

/-- Instructions 1353..1358, pc 1804..1819. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 681 2 987,
   pushAt 682 2 256,
   pushAt 683 2 1280,
   pushAt 684 2 256,
   pushAt 685 2 3550,
   opAt 686 .JUMP]

/-- Instructions 1359..1379, pc 1820..1806. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 687 .JUMPDEST,
   opAt 688 (.Dup ⟨0, by decide⟩),
   opAt 689 (.Dup ⟨2, by decide⟩),
   opAt 690 .SUB,
   pushAt 691 1 5,
   opAt 692 .SHL,
   opAt 693 (.Dup ⟨5, by decide⟩),
   opAt 694 .SUB,
   pushAt 695 1 96,
   opAt 696 .ADD,
   opAt 697 .CALLDATALOAD,
   opAt 698 (.Dup ⟨3, by decide⟩),
   pushAt 699 2 736,
   opAt 700 .ADD,
   opAt 701 .MSTORE,
   pushAt 702 2 1022,
   pushAt 703 2 256,
   pushAt 704 2 768,
   pushAt 705 2 256,
   pushAt 706 2 1475,
   opAt 707 .JUMP]

/-- Instructions 1332..1384, pc 1728..1814. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 708 .JUMPDEST,
   pushAt 709 1 1,
   opAt 710 .ADD,
   pushAt 711 2 963,
   opAt 712 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
