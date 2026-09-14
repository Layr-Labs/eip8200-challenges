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
  [opAt 855 .JUMPDEST,
   opAt 856 (.Dup ⟨3, by decide⟩),
   opAt 857 (.Dup ⟨1, by decide⟩),
   opAt 858 .MLOAD,
   opAt 859 (.Dup ⟨1, by decide⟩),
   opAt 860 (.Dup ⟨1, by decide⟩),
   opAt 861 .MUL,
   opAt 862 (.Swap ⟨1, by decide⟩),
   pushAt 863 0 0,
   opAt 864 .NOT,
   opAt 865 (.Swap ⟨1, by decide⟩),
   opAt 866 .MULMOD,
   opAt 867 (.Dup ⟨1, by decide⟩),
   opAt 868 (.Dup ⟨1, by decide⟩),
   opAt 869 .LT,
   opAt 870 (.Dup ⟨2, by decide⟩),
   opAt 871 .ADD,
   opAt 872 (.Swap ⟨0, by decide⟩),
   opAt 873 .SUB,
   opAt 874 (.Dup ⟨3, by decide⟩),
   opAt 875 .MLOAD,
   opAt 876 (.Swap ⟨1, by decide⟩),
   opAt 877 (.Dup ⟨2, by decide⟩),
   opAt 878 .ADD,
   opAt 879 (.Swap ⟨1, by decide⟩),
   opAt 880 (.Dup ⟨2, by decide⟩),
   opAt 881 .LT,
   opAt 882 .ADD,
   opAt 883 (.Swap ⟨0, by decide⟩),
   opAt 884 (.Dup ⟨4, by decide⟩),
   opAt 885 .ADD,
   opAt 886 (.Swap ⟨3, by decide⟩),
   opAt 887 (.Dup ⟨4, by decide⟩),
   opAt 888 .LT,
   opAt 889 .ADD,
   opAt 890 (.Swap ⟨2, by decide⟩),
   opAt 891 (.Dup ⟨2, by decide⟩),
   opAt 892 .MSTORE,
   pushAt 893 1 31,
   opAt 894 .NOT,
   opAt 895 .ADD,
   opAt 896 (.Swap ⟨0, by decide⟩),
   pushAt 897 1 31,
   opAt 898 .NOT,
   opAt 899 .ADD,
   opAt 900 (.Swap ⟨0, by decide⟩),
   opAt 901 (.Dup ⟨5, by decide⟩),
   opAt 902 (.Dup ⟨1, by decide⟩),
   opAt 903 .GT,
   pushAt 904 2 1252,
   opAt 905 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
