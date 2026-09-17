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
  [opAt 816 .JUMPDEST,
   opAt 817 (.Dup ⟨0, by decide⟩),
   opAt 818 .MLOAD,
   opAt 819 (.Dup ⟨2, by decide⟩),
   opAt 820 .MLOAD,
   opAt 821 (.Dup ⟨1, by decide⟩),
   opAt 822 (.Dup ⟨1, by decide⟩),
   opAt 823 .GT,
   opAt 824 (.Swap ⟨1, by decide⟩),
   opAt 825 .SUB,
   opAt 826 (.Dup ⟨5, by decide⟩),
   opAt 827 (.Dup ⟨1, by decide⟩),
   opAt 828 .SUB,
   opAt 829 (.Swap ⟨0, by decide⟩),
   opAt 830 (.Dup ⟨6, by decide⟩),
   opAt 831 .GT,
   opAt 832 (.Swap ⟨0, by decide⟩),
   opAt 833 (.Swap ⟨1, by decide⟩),
   opAt 834 .OR,
   opAt 835 (.Swap ⟨4, by decide⟩),
   opAt 836 .POP,
   opAt 837 (.Dup ⟨3, by decide⟩),
   opAt 838 .MSTORE,
   pushAt 839 1 31,
   opAt 840 .NOT,
   opAt 841 .ADD,
   opAt 842 (.Swap ⟨0, by decide⟩),
   pushAt 843 1 31,
   opAt 844 .NOT,
   opAt 845 .ADD,
   opAt 846 (.Swap ⟨0, by decide⟩),
   opAt 847 (.Swap ⟨1, by decide⟩),
   pushAt 848 1 31,
   opAt 849 .NOT,
   opAt 850 .ADD,
   opAt 851 (.Swap ⟨1, by decide⟩),
   pushAt 852 2 2080,
   opAt 853 (.Dup ⟨1, by decide⟩),
   opAt 854 .GT,
   pushAt 855 2 1182,
   opAt 856 .JUMPI]

/-- Live instructions 1851..1866, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 857 .POP,
   opAt 858 .POP,
   opAt 859 .POP,
   opAt 860 .ISZERO,
   pushAt 861 2 2080,
   opAt 862 .MLOAD,
   opAt 863 .OR,
   pushAt 864 2 319,
   opAt 865 .NOT,
   opAt 866 .MUL,
   pushAt 867 2 2112,
   opAt 868 .ADD,
   pushAt 869 2 2688,
   opAt 870 .MLOAD,
   opAt 871 (.Swap ⟨1, by decide⟩),
   opAt 872 .MCOPY,
   opAt 873 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
