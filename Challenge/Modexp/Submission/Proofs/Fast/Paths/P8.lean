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
  [opAt 776 .JUMPDEST,
   opAt 777 (.Dup ⟨3, by decide⟩),
   opAt 778 (.Dup ⟨1, by decide⟩),
   opAt 779 .MLOAD,
   opAt 780 (.Dup ⟨1, by decide⟩),
   opAt 781 (.Dup ⟨1, by decide⟩),
   opAt 782 .MUL,
   opAt 783 (.Swap ⟨1, by decide⟩),
   pushAt 784 0 0,
   opAt 785 .NOT,
   opAt 786 (.Swap ⟨1, by decide⟩),
   opAt 787 .MULMOD,
   opAt 788 (.Dup ⟨1, by decide⟩),
   opAt 789 (.Dup ⟨1, by decide⟩),
   opAt 790 .LT,
   opAt 791 (.Dup ⟨2, by decide⟩),
   opAt 792 .ADD,
   opAt 793 (.Swap ⟨0, by decide⟩),
   opAt 794 .SUB,
   opAt 795 (.Dup ⟨3, by decide⟩),
   opAt 796 .MLOAD,
   opAt 797 (.Swap ⟨1, by decide⟩),
   opAt 798 (.Dup ⟨2, by decide⟩),
   opAt 799 .ADD,
   opAt 800 (.Swap ⟨1, by decide⟩),
   opAt 801 (.Dup ⟨2, by decide⟩),
   opAt 802 .LT,
   opAt 803 .ADD,
   opAt 804 (.Swap ⟨0, by decide⟩),
   opAt 805 (.Dup ⟨4, by decide⟩),
   opAt 806 .ADD,
   opAt 807 (.Swap ⟨3, by decide⟩),
   opAt 808 (.Dup ⟨4, by decide⟩),
   opAt 809 .LT,
   opAt 810 .ADD,
   opAt 811 (.Swap ⟨2, by decide⟩),
   opAt 812 (.Dup ⟨2, by decide⟩),
   opAt 813 .MSTORE,
   pushAt 814 1 32,
   opAt 815 .SUB,
   opAt 816 (.Swap ⟨0, by decide⟩),
   opAt 817 .JUMPDEST,
   pushAt 818 1 32,
   opAt 819 .SUB,
   opAt 820 (.Swap ⟨0, by decide⟩),
   opAt 821 .JUMPDEST,
   opAt 822 (.Dup ⟨5, by decide⟩),
   opAt 823 (.Dup ⟨1, by decide⟩),
   opAt 824 .GT,
   pushAt 825 2 1135,
   opAt 826 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
