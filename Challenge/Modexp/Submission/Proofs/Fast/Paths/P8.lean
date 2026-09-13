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
  [opAt 854 .JUMPDEST,
   opAt 855 (.Dup ⟨3, by decide⟩),
   opAt 856 (.Dup ⟨1, by decide⟩),
   opAt 857 .MLOAD,
   opAt 858 (.Dup ⟨1, by decide⟩),
   opAt 859 (.Dup ⟨1, by decide⟩),
   opAt 860 .MUL,
   opAt 861 (.Swap ⟨1, by decide⟩),
   pushAt 862 0 0,
   opAt 863 .NOT,
   opAt 864 (.Swap ⟨1, by decide⟩),
   opAt 865 .MULMOD,
   opAt 866 (.Dup ⟨1, by decide⟩),
   opAt 867 (.Dup ⟨1, by decide⟩),
   opAt 868 .LT,
   opAt 869 (.Dup ⟨2, by decide⟩),
   opAt 870 .ADD,
   opAt 871 (.Swap ⟨0, by decide⟩),
   opAt 872 .SUB,
   opAt 873 (.Dup ⟨3, by decide⟩),
   opAt 874 .MLOAD,
   opAt 875 (.Swap ⟨1, by decide⟩),
   opAt 876 (.Dup ⟨2, by decide⟩),
   opAt 877 .ADD,
   opAt 878 (.Swap ⟨1, by decide⟩),
   opAt 879 (.Dup ⟨2, by decide⟩),
   opAt 880 .LT,
   opAt 881 .ADD,
   opAt 882 (.Swap ⟨0, by decide⟩),
   opAt 883 (.Dup ⟨4, by decide⟩),
   opAt 884 .ADD,
   opAt 885 (.Swap ⟨3, by decide⟩),
   opAt 886 (.Dup ⟨4, by decide⟩),
   opAt 887 .LT,
   opAt 888 .ADD,
   opAt 889 (.Swap ⟨2, by decide⟩),
   opAt 890 (.Dup ⟨2, by decide⟩),
   opAt 891 .MSTORE,
   pushAt 892 1 31,
   opAt 893 .NOT,
   opAt 894 .ADD,
   opAt 895 (.Swap ⟨0, by decide⟩),
   pushAt 896 1 31,
   opAt 897 .NOT,
   opAt 898 .ADD,
   opAt 899 (.Swap ⟨0, by decide⟩),
   opAt 900 (.Dup ⟨5, by decide⟩),
   opAt 901 (.Dup ⟨1, by decide⟩),
   opAt 902 .GT,
   pushAt 903 2 1252,
   opAt 904 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
