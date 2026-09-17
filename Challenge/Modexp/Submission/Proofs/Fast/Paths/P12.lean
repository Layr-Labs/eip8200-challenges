import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1754..1809). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1754..1788, pc 2380..2769. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 769 .JUMPDEST,
   opAt 770 (.Dup ⟨1 , by decide⟩),
   opAt 771 .MLOAD,
   opAt 772 (.Dup ⟨3 , by decide⟩),
   opAt 773 .MLOAD,
   opAt 774 (.Dup ⟨1 , by decide⟩),
   opAt 775 .ADD,
   opAt 776 (.Swap ⟨0 , by decide⟩),
   opAt 777 (.Dup ⟨1 , by decide⟩),
   opAt 778 .LT,
   opAt 779 (.Swap ⟨0 , by decide⟩),
   opAt 780 (.Dup ⟨5 , by decide⟩),
   opAt 781 .ADD,
   opAt 782 (.Swap ⟨4 , by decide⟩),
   opAt 783 (.Dup ⟨5 , by decide⟩),
   opAt 784 .LT,
   opAt 785 .OR,
   opAt 786 (.Swap ⟨3 , by decide⟩),
   opAt 787 (.Dup ⟨1 , by decide⟩),
   opAt 788 .MSTORE,
   pushAt 789 1 32,
   pushAt 790 1 32,
   pushAt 791 1 32,
   opAt 792 (.Swap ⟨2 , by decide⟩),
   opAt 793 .SUB,
   opAt 794 (.Swap ⟨2 , by decide⟩),
   opAt 795 .SUB,
   opAt 796 (.Swap ⟨2 , by decide⟩),
   opAt 797 .SUB,
   opAt 798 (.Swap ⟨1 , by decide⟩),
   opAt 799 (.Swap ⟨0 , by decide⟩),
   pushAt 800 2 2080,
   opAt 801 (.Dup ⟨1 , by decide⟩),
   opAt 802 .GT,
   pushAt 803 2 1128,
   opAt 804 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2431. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 805 .POP,
   opAt 806 .POP,
   opAt 807 .POP,
   pushAt 808 2 2080,
   opAt 809 .MSTORE,
   pushAt 810 2 3963,
   opAt 811 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
