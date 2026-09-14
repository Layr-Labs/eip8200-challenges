import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1551..1598). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1551..1598, pc 2122..2128. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 774 .JUMPDEST,
   opAt 775 (.Dup ⟨3, by decide⟩),
   opAt 776 (.Dup ⟨1, by decide⟩),
   opAt 777 .MLOAD,
   opAt 778 (.Dup ⟨1, by decide⟩),
   opAt 779 (.Dup ⟨1, by decide⟩),
   opAt 780 .MUL,
   opAt 781 (.Swap ⟨1, by decide⟩),
   pushAt 782 0 0,
   opAt 783 .NOT,
   opAt 784 (.Swap ⟨1, by decide⟩),
   opAt 785 .MULMOD,
   opAt 786 (.Dup ⟨1, by decide⟩),
   opAt 787 (.Dup ⟨1, by decide⟩),
   opAt 788 .LT,
   opAt 789 (.Dup ⟨2, by decide⟩),
   opAt 790 .ADD,
   opAt 791 (.Swap ⟨0, by decide⟩),
   opAt 792 .SUB,
   opAt 793 (.Dup ⟨3, by decide⟩),
   opAt 794 .MLOAD,
   opAt 795 (.Swap ⟨1, by decide⟩),
   opAt 796 (.Dup ⟨2, by decide⟩),
   opAt 797 .ADD,
   opAt 798 (.Swap ⟨1, by decide⟩),
   opAt 799 (.Dup ⟨2, by decide⟩),
   opAt 800 .LT,
   opAt 801 .ADD,
   opAt 802 (.Swap ⟨0, by decide⟩),
   opAt 803 (.Dup ⟨4, by decide⟩),
   opAt 804 .ADD,
   opAt 805 (.Swap ⟨3, by decide⟩),
   opAt 806 (.Dup ⟨4, by decide⟩),
   opAt 807 .LT,
   opAt 808 .ADD,
   opAt 809 (.Swap ⟨2, by decide⟩),
   opAt 810 (.Dup ⟨2, by decide⟩),
   opAt 811 .MSTORE,
   pushAt 812 1 31,
   opAt 813 .NOT,
   opAt 814 .ADD,
   opAt 815 (.Swap ⟨0, by decide⟩),
   pushAt 816 1 31,
   opAt 817 .NOT,
   opAt 818 .ADD,
   opAt 819 (.Swap ⟨0, by decide⟩),
   opAt 820 (.Dup ⟨5, by decide⟩),
   opAt 821 (.Dup ⟨1, by decide⟩),
   opAt 822 .GT,
   pushAt 823 2 1134,
   opAt 824 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
