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
  [opAt 878 .JUMPDEST,
   opAt 879 (.Dup ⟨0, by decide⟩),
   opAt 880 .MLOAD,
   pushAt 881 0 0,
   opAt 882 .NOT,
   opAt 883 (.Dup ⟨5, by decide⟩),
   opAt 884 (.Dup ⟨2, by decide⟩),
   opAt 885 .MUL,
   opAt 886 (.Swap ⟨1, by decide⟩),
   opAt 887 (.Dup ⟨6, by decide⟩),
   opAt 888 .MULMOD,
   opAt 889 (.Dup ⟨1, by decide⟩),
   opAt 890 (.Dup ⟨1, by decide⟩),
   opAt 891 .LT,
   opAt 892 .SUB,
   opAt 893 (.Dup ⟨4, by decide⟩),
   opAt 894 (.Dup ⟨2, by decide⟩),
   opAt 895 .ADD,
   opAt 896 (.Dup ⟨0, by decide⟩),
   opAt 897 (.Swap ⟨5, by decide⟩),
   opAt 898 .GT,
   opAt 899 .SUB,
   opAt 900 .SUB,
   opAt 901 (.Dup ⟨3, by decide⟩),
   opAt 902 (.Dup ⟨3, by decide⟩),
   opAt 903 .MLOAD,
   opAt 904 .ADD,
   opAt 905 (.Dup ⟨0, by decide⟩),
   opAt 906 (.Swap ⟨4, by decide⟩),
   opAt 907 .GT,
   opAt 908 .ADD,
   opAt 909 (.Swap ⟨2, by decide⟩),
   pushAt 910 1 32,
   opAt 911 (.Dup ⟨3, by decide⟩),
   pushAt 912 1 31,
   opAt 913 .NOT,
   opAt 914 .ADD,
   opAt 915 (.Swap ⟨3, by decide⟩),
   opAt 916 .ADD,
   opAt 917 .MSTORE,
   pushAt 918 1 31,
   opAt 919 .NOT,
   opAt 920 .ADD,
   pushAt 921 2 2080,
   opAt 922 (.Dup ⟨2, by decide⟩),
   opAt 923 .GT,
   pushAt 924 2 1259,
   opAt 925 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
