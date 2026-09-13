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
  [opAt 861 .JUMPDEST,
   opAt 862 (.Dup ⟨3, by decide⟩),
   opAt 863 (.Dup ⟨1, by decide⟩),
   opAt 864 .MLOAD,
   opAt 865 (.Dup ⟨1, by decide⟩),
   opAt 866 (.Dup ⟨1, by decide⟩),
   opAt 867 .MUL,
   opAt 868 (.Swap ⟨1, by decide⟩),
   pushAt 869 0 0,
   opAt 870 .NOT,
   opAt 871 (.Swap ⟨1, by decide⟩),
   opAt 872 .MULMOD,
   opAt 873 (.Dup ⟨1, by decide⟩),
   opAt 874 (.Dup ⟨1, by decide⟩),
   opAt 875 .LT,
   opAt 876 (.Dup ⟨2, by decide⟩),
   opAt 877 .ADD,
   opAt 878 (.Swap ⟨0, by decide⟩),
   opAt 879 .SUB,
   opAt 880 (.Dup ⟨3, by decide⟩),
   opAt 881 .MLOAD,
   opAt 882 (.Swap ⟨1, by decide⟩),
   opAt 883 (.Dup ⟨2, by decide⟩),
   opAt 884 .ADD,
   opAt 885 (.Swap ⟨1, by decide⟩),
   opAt 886 (.Dup ⟨2, by decide⟩),
   opAt 887 .LT,
   opAt 888 .ADD,
   opAt 889 (.Swap ⟨0, by decide⟩),
   opAt 890 (.Dup ⟨4, by decide⟩),
   opAt 891 .ADD,
   opAt 892 (.Swap ⟨3, by decide⟩),
   opAt 893 (.Dup ⟨4, by decide⟩),
   opAt 894 .LT,
   opAt 895 .ADD,
   opAt 896 (.Swap ⟨2, by decide⟩),
   opAt 897 (.Dup ⟨2, by decide⟩),
   opAt 898 .MSTORE,
   pushAt 899 1 31,
   opAt 900 .NOT,
   opAt 901 .ADD,
   opAt 902 (.Swap ⟨0, by decide⟩),
   pushAt 903 1 31,
   opAt 904 .NOT,
   opAt 905 .ADD,
   opAt 906 (.Swap ⟨0, by decide⟩),
   opAt 907 (.Dup ⟨5, by decide⟩),
   opAt 908 (.Dup ⟨1, by decide⟩),
   opAt 909 .GT,
   pushAt 910 2 1268,
   opAt 911 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
