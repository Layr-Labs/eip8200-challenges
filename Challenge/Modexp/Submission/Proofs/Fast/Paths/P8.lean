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
  [opAt 853 .JUMPDEST,
   opAt 854 (.Dup ⟨3, by decide⟩),
   opAt 855 (.Dup ⟨1, by decide⟩),
   opAt 856 .MLOAD,
   opAt 857 (.Dup ⟨1, by decide⟩),
   opAt 858 (.Dup ⟨1, by decide⟩),
   opAt 859 .MUL,
   opAt 860 (.Swap ⟨1, by decide⟩),
   pushAt 861 0 0,
   opAt 862 .NOT,
   opAt 863 (.Swap ⟨1, by decide⟩),
   opAt 864 .MULMOD,
   opAt 865 (.Dup ⟨1, by decide⟩),
   opAt 866 (.Dup ⟨1, by decide⟩),
   opAt 867 .LT,
   opAt 868 (.Dup ⟨2, by decide⟩),
   opAt 869 .ADD,
   opAt 870 (.Swap ⟨0, by decide⟩),
   opAt 871 .SUB,
   opAt 872 (.Dup ⟨3, by decide⟩),
   opAt 873 .MLOAD,
   opAt 874 (.Swap ⟨1, by decide⟩),
   opAt 875 (.Dup ⟨2, by decide⟩),
   opAt 876 .ADD,
   opAt 877 (.Swap ⟨1, by decide⟩),
   opAt 878 (.Dup ⟨2, by decide⟩),
   opAt 879 .LT,
   opAt 880 .ADD,
   opAt 881 (.Swap ⟨0, by decide⟩),
   opAt 882 (.Dup ⟨4, by decide⟩),
   opAt 883 .ADD,
   opAt 884 (.Swap ⟨3, by decide⟩),
   opAt 885 (.Dup ⟨4, by decide⟩),
   opAt 886 .LT,
   opAt 887 .ADD,
   opAt 888 (.Swap ⟨2, by decide⟩),
   opAt 889 (.Dup ⟨2, by decide⟩),
   opAt 890 .MSTORE,
   pushAt 891 1 31,
   opAt 892 .NOT,
   opAt 893 .ADD,
   opAt 894 (.Swap ⟨0, by decide⟩),
   pushAt 895 1 31,
   opAt 896 .NOT,
   opAt 897 .ADD,
   opAt 898 (.Swap ⟨0, by decide⟩),
   opAt 899 (.Dup ⟨5, by decide⟩),
   opAt 900 (.Dup ⟨1, by decide⟩),
   opAt 901 .GT,
   pushAt 902 2 1251,
   opAt 903 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
