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
  [pushAt 674 2 2466,
   opAt 675 .JUMP]

/-- Instructions 1216..1352, pc 1795..1803. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 676 .JUMPDEST,
   opAt 677 (.Dup ⟨1, by decide⟩),
   opAt 678 (.Dup ⟨1, by decide⟩),
   opAt 679 .EQ,
   pushAt 680 2 1042,
   opAt 681 .JUMPI]

/-- Instructions 1353..1358, pc 1804..1819. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 682 2 999,
   pushAt 683 2 256,
   pushAt 684 2 1280,
   pushAt 685 2 256,
   pushAt 686 2 3536,
   opAt 687 .JUMP]

/-- Instructions 1359..1379, pc 1820..1806. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 688 .JUMPDEST,
   opAt 689 (.Dup ⟨0, by decide⟩),
   opAt 690 (.Dup ⟨2, by decide⟩),
   opAt 691 .SUB,
   pushAt 692 1 5,
   opAt 693 .SHL,
   opAt 694 (.Dup ⟨5, by decide⟩),
   opAt 695 .SUB,
   pushAt 696 1 96,
   opAt 697 .ADD,
   opAt 698 .CALLDATALOAD,
   opAt 699 (.Dup ⟨3, by decide⟩),
   pushAt 700 2 736,
   opAt 701 .ADD,
   opAt 702 .MSTORE,
   pushAt 703 2 1034,
   pushAt 704 2 256,
   pushAt 705 2 768,
   pushAt 706 2 256,
   pushAt 707 2 1487,
   opAt 708 .JUMP]

/-- Instructions 1332..1384, pc 1728..1814. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 709 .JUMPDEST,
   pushAt 710 1 1,
   opAt 711 .ADD,
   pushAt 712 2 975,
   opAt 713 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
