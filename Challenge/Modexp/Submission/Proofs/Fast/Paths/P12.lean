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
  [opAt 773 .JUMPDEST,
   opAt 774 (.Dup ⟨1 , by decide⟩),
   opAt 775 .MLOAD,
   opAt 776 (.Dup ⟨3 , by decide⟩),
   opAt 777 .MLOAD,
   opAt 778 (.Dup ⟨1 , by decide⟩),
   opAt 779 .ADD,
   opAt 780 (.Swap ⟨0 , by decide⟩),
   opAt 781 (.Dup ⟨1 , by decide⟩),
   opAt 782 .LT,
   opAt 783 (.Swap ⟨0 , by decide⟩),
   opAt 784 (.Dup ⟨5 , by decide⟩),
   opAt 785 .ADD,
   opAt 786 (.Swap ⟨4 , by decide⟩),
   opAt 787 (.Dup ⟨5 , by decide⟩),
   opAt 788 .LT,
   opAt 789 .OR,
   opAt 790 (.Swap ⟨3 , by decide⟩),
   opAt 791 (.Dup ⟨1 , by decide⟩),
   opAt 792 .MSTORE,
   pushAt 793 1 32,
   pushAt 794 1 32,
   pushAt 795 1 32,
   opAt 796 (.Swap ⟨2 , by decide⟩),
   opAt 797 .SUB,
   opAt 798 (.Swap ⟨2 , by decide⟩),
   opAt 799 .SUB,
   opAt 800 (.Swap ⟨2 , by decide⟩),
   opAt 801 .SUB,
   opAt 802 (.Swap ⟨1 , by decide⟩),
   opAt 803 (.Swap ⟨0 , by decide⟩),
   pushAt 804 2 2080,
   opAt 805 (.Dup ⟨1 , by decide⟩),
   opAt 806 .GT,
   pushAt 807 2 1128,
   opAt 808 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2431. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 809 .POP,
   opAt 810 .POP,
   opAt 811 .POP,
   pushAt 812 2 2080,
   opAt 813 .MSTORE,
   pushAt 814 2 3963,
   opAt 815 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
