import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1644..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1644..1568, pc 2198..2305. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 876 .JUMPDEST,
   opAt 877 (.Dup ⟨0, by decide⟩),
   opAt 878 .MLOAD,
   pushAt 879 0 0,
   opAt 880 .NOT,
   opAt 881 (.Dup ⟨5, by decide⟩),
   opAt 882 (.Dup ⟨2, by decide⟩),
   opAt 883 .MUL,
   opAt 884 (.Swap ⟨1, by decide⟩),
   opAt 885 (.Dup ⟨6, by decide⟩),
   opAt 886 .MULMOD,
   opAt 887 (.Dup ⟨1, by decide⟩),
   opAt 888 (.Dup ⟨1, by decide⟩),
   opAt 889 .LT,
   opAt 890 .SUB,
   opAt 891 (.Dup ⟨4, by decide⟩),
   opAt 892 (.Dup ⟨2, by decide⟩),
   opAt 893 .ADD,
   opAt 894 (.Dup ⟨0, by decide⟩),
   opAt 895 (.Swap ⟨5, by decide⟩),
   opAt 896 .GT,
   opAt 897 .SUB,
   opAt 898 .SUB,
   opAt 899 (.Dup ⟨3, by decide⟩),
   opAt 900 (.Dup ⟨3, by decide⟩),
   opAt 901 .MLOAD,
   opAt 902 .ADD,
   opAt 903 (.Dup ⟨0, by decide⟩),
   opAt 904 (.Swap ⟨4, by decide⟩),
   opAt 905 .GT,
   opAt 906 .ADD,
   opAt 907 (.Swap ⟨2, by decide⟩),
   pushAt 908 1 32,
   opAt 909 (.Dup ⟨3, by decide⟩),
   pushAt 910 1 31,
   opAt 911 .NOT,
   opAt 912 .ADD,
   opAt 913 (.Swap ⟨3, by decide⟩),
   opAt 914 .ADD,
   opAt 915 .MSTORE,
   pushAt 916 1 31,
   opAt 917 .NOT,
   opAt 918 .ADD,
   pushAt 919 2 2080,
   opAt 920 (.Dup ⟨2, by decide⟩),
   opAt 921 .GT,
   pushAt 922 2 1258,
   opAt 923 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
