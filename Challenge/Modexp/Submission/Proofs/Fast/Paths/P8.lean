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
  [opAt 856 .JUMPDEST,
   opAt 857 (.Dup ⟨3, by decide⟩),
   opAt 858 (.Dup ⟨1, by decide⟩),
   opAt 859 .MLOAD,
   opAt 860 (.Dup ⟨1, by decide⟩),
   opAt 861 (.Dup ⟨1, by decide⟩),
   opAt 862 .MUL,
   opAt 863 (.Swap ⟨1, by decide⟩),
   pushAt 864 0 0,
   opAt 865 .NOT,
   opAt 866 (.Swap ⟨1, by decide⟩),
   opAt 867 .MULMOD,
   opAt 868 (.Dup ⟨1, by decide⟩),
   opAt 869 (.Dup ⟨1, by decide⟩),
   opAt 870 .LT,
   opAt 871 (.Dup ⟨2, by decide⟩),
   opAt 872 .ADD,
   opAt 873 (.Swap ⟨0, by decide⟩),
   opAt 874 .SUB,
   opAt 875 (.Dup ⟨3, by decide⟩),
   opAt 876 .MLOAD,
   opAt 877 (.Swap ⟨1, by decide⟩),
   opAt 878 (.Dup ⟨2, by decide⟩),
   opAt 879 .ADD,
   opAt 880 (.Swap ⟨1, by decide⟩),
   opAt 881 (.Dup ⟨2, by decide⟩),
   opAt 882 .LT,
   opAt 883 .ADD,
   opAt 884 (.Swap ⟨0, by decide⟩),
   opAt 885 (.Dup ⟨4, by decide⟩),
   opAt 886 .ADD,
   opAt 887 (.Swap ⟨3, by decide⟩),
   opAt 888 (.Dup ⟨4, by decide⟩),
   opAt 889 .LT,
   opAt 890 .ADD,
   opAt 891 (.Swap ⟨2, by decide⟩),
   opAt 892 (.Dup ⟨2, by decide⟩),
   opAt 893 .MSTORE,
   pushAt 894 1 31,
   opAt 895 .NOT,
   opAt 896 .ADD,
   opAt 897 (.Swap ⟨0, by decide⟩),
   pushAt 898 1 31,
   opAt 899 .NOT,
   opAt 900 .ADD,
   opAt 901 (.Swap ⟨0, by decide⟩),
   opAt 902 (.Dup ⟨5, by decide⟩),
   opAt 903 (.Dup ⟨1, by decide⟩),
   opAt 904 .GT,
   pushAt 905 2 1264,
   opAt 906 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
