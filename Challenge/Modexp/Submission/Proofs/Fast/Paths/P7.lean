import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1451..1550). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1451..1505, pc 2053..2062. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 729 .JUMPDEST,
   pushAt 730 1 1,
   opAt 731 (.Swap ⟨0, by decide⟩),
   opAt 732 .SUB,
   opAt 733 (.Dup ⟨0, by decide⟩),
   pushAt 734 2 1062,
   opAt 735 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2065. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 736 .POP,
   opAt 737 .POP,
   opAt 738 .JUMP]

/-- Instructions 1509..1487, pc 2066..2100. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 739 .JUMPDEST,
   pushAt 740 2 2688,
   opAt 741 .MLOAD,
   opAt 742 (.Dup ⟨0, by decide⟩),
   pushAt 743 1 64,
   opAt 744 .ADD,
   opAt 745 .CALLDATASIZE,
   pushAt 746 2 2048,
   opAt 747 .CALLDATACOPY,
   opAt 748 (.Dup ⟨0, by decide⟩),
   opAt 749 (.Dup ⟨3, by decide⟩),
   opAt 750 .ADD,
   pushAt 751 1 32,
   opAt 752 (.Swap ⟨0, by decide⟩),
   opAt 753 .SUB,
   pushAt 754 1 32,
   opAt 755 (.Dup ⟨4, by decide⟩),
   opAt 756 .SUB,
   opAt 757 (.Swap ⟨3, by decide⟩),
   opAt 758 .POP,
   opAt 759 (.Swap ⟨0, by decide⟩),
   opAt 760 .POP,
   pushAt 761 1 32,
   opAt 762 (.Dup ⟨2, by decide⟩),
   opAt 763 .SUB,
   opAt 764 (.Swap ⟨1, by decide⟩),
   opAt 765 .POP]

/-- Instructions 1536..1550, pc 2101..2121. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 766 .JUMPDEST,
   opAt 767 (.Dup ⟨0, by decide⟩),
   opAt 768 .MLOAD,
   pushAt 769 0 0,
   pushAt 770 2 2784,
   opAt 771 .MLOAD,
   opAt 772 (.Dup ⟨4, by decide⟩),
   pushAt 773 2 2688,
   opAt 774 .MLOAD,
   opAt 775 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
