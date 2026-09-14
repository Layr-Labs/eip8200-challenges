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
  [opAt 727 .JUMPDEST,
   pushAt 728 1 0,
   opAt 729 .NOT,
   opAt 730 .ADD,
   opAt 731 (.Dup ⟨0, by decide⟩),
   pushAt 732 2 1061,
   opAt 733 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2065. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 734 .POP,
   opAt 735 .POP,
   opAt 736 .JUMP]

/-- Instructions 1509..1487, pc 2066..2100. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 737 .JUMPDEST,
   pushAt 738 2 2688,
   opAt 739 .MLOAD,
   opAt 740 (.Dup ⟨0, by decide⟩),
   pushAt 741 1 64,
   opAt 742 .ADD,
   opAt 743 .CALLDATASIZE,
   pushAt 744 2 2048,
   opAt 745 .CALLDATACOPY,
   opAt 746 (.Dup ⟨0, by decide⟩),
   opAt 747 (.Dup ⟨3, by decide⟩),
   opAt 748 .ADD,
   pushAt 749 1 31,
   opAt 750 .NOT,
   opAt 751 .ADD,
   pushAt 752 1 32,
   opAt 753 (.Dup ⟨4, by decide⟩),
   opAt 754 .SUB,
   opAt 755 (.Swap ⟨3, by decide⟩),
   opAt 756 .POP,
   opAt 757 (.Swap ⟨0, by decide⟩),
   opAt 758 .POP,
   pushAt 759 1 32,
   opAt 760 (.Dup ⟨2, by decide⟩),
   opAt 761 .SUB,
   opAt 762 (.Swap ⟨1, by decide⟩),
   opAt 763 .POP]

/-- Instructions 1536..1550, pc 2101..2121. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 764 .JUMPDEST,
   opAt 765 (.Dup ⟨0, by decide⟩),
   opAt 766 .MLOAD,
   pushAt 767 0 0,
   pushAt 768 2 2784,
   opAt 769 .MLOAD,
   opAt 770 (.Dup ⟨4, by decide⟩),
   pushAt 771 2 2688,
   opAt 772 .MLOAD,
   opAt 773 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
