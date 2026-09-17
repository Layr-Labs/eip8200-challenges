import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1810..1820). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1810..1850, pc 2411..2608. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 812 .JUMPDEST,
   opAt 813 (.Dup ⟨0, by decide⟩),
   opAt 814 .MLOAD,
   opAt 815 (.Dup ⟨2, by decide⟩),
   opAt 816 .MLOAD,
   opAt 817 (.Dup ⟨1, by decide⟩),
   opAt 818 (.Dup ⟨1, by decide⟩),
   opAt 819 .GT,
   opAt 820 (.Swap ⟨1, by decide⟩),
   opAt 821 .SUB,
   opAt 822 (.Dup ⟨5, by decide⟩),
   opAt 823 (.Dup ⟨1, by decide⟩),
   opAt 824 .SUB,
   opAt 825 (.Swap ⟨0, by decide⟩),
   opAt 826 (.Dup ⟨6, by decide⟩),
   opAt 827 .GT,
   opAt 828 (.Swap ⟨0, by decide⟩),
   opAt 829 (.Swap ⟨1, by decide⟩),
   opAt 830 .OR,
   opAt 831 (.Swap ⟨4, by decide⟩),
   opAt 832 .POP,
   opAt 833 (.Dup ⟨3, by decide⟩),
   opAt 834 .MSTORE,
   pushAt 835 1 31,
   opAt 836 .NOT,
   opAt 837 .ADD,
   opAt 838 (.Swap ⟨0, by decide⟩),
   pushAt 839 1 31,
   opAt 840 .NOT,
   opAt 841 .ADD,
   opAt 842 (.Swap ⟨0, by decide⟩),
   opAt 843 (.Swap ⟨1, by decide⟩),
   pushAt 844 1 31,
   opAt 845 .NOT,
   opAt 846 .ADD,
   opAt 847 (.Swap ⟨1, by decide⟩),
   pushAt 848 2 2080,
   opAt 849 (.Dup ⟨1, by decide⟩),
   opAt 850 .GT,
   pushAt 851 2 1182,
   opAt 852 .JUMPI]

/-- Live instructions 1851..1866, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 853 .POP,
   opAt 854 .POP,
   opAt 855 .POP,
   opAt 856 .ISZERO,
   pushAt 857 2 2080,
   opAt 858 .MLOAD,
   opAt 859 .OR,
   pushAt 860 2 319,
   opAt 861 .NOT,
   opAt 862 .MUL,
   pushAt 863 2 2112,
   opAt 864 .ADD,
   pushAt 865 2 2688,
   opAt 866 .MLOAD,
   opAt 867 (.Swap ⟨1, by decide⟩),
   opAt 868 .MCOPY,
   opAt 869 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
