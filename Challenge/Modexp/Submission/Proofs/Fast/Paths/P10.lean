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
  [opAt 955 .JUMPDEST,
   opAt 956 (.Dup ⟨0, by decide⟩),
   opAt 957 .MLOAD,
   pushAt 958 0 0,
   opAt 959 .NOT,
   opAt 960 (.Dup ⟨5, by decide⟩),
   opAt 961 (.Dup ⟨2, by decide⟩),
   opAt 962 .MUL,
   opAt 963 (.Swap ⟨1, by decide⟩),
   opAt 964 (.Dup ⟨6, by decide⟩),
   opAt 965 .MULMOD,
   opAt 966 (.Dup ⟨1, by decide⟩),
   opAt 967 (.Dup ⟨1, by decide⟩),
   opAt 968 .LT,
   opAt 969 .SUB,
   opAt 970 (.Dup ⟨4, by decide⟩),
   opAt 971 (.Dup ⟨2, by decide⟩),
   opAt 972 .ADD,
   opAt 973 (.Dup ⟨0, by decide⟩),
   opAt 974 (.Swap ⟨5, by decide⟩),
   opAt 975 .GT,
   opAt 976 .SUB,
   opAt 977 .SUB,
   opAt 978 (.Dup ⟨3, by decide⟩),
   opAt 979 (.Dup ⟨3, by decide⟩),
   opAt 980 .MLOAD,
   opAt 981 .ADD,
   opAt 982 (.Dup ⟨0, by decide⟩),
   opAt 983 (.Swap ⟨4, by decide⟩),
   opAt 984 .GT,
   opAt 985 .ADD,
   opAt 986 (.Swap ⟨2, by decide⟩),
   pushAt 987 1 32,
   opAt 988 (.Dup ⟨3, by decide⟩),
   pushAt 989 1 31,
   opAt 990 .NOT,
   opAt 991 .ADD,
   opAt 992 (.Swap ⟨3, by decide⟩),
   opAt 993 .ADD,
   opAt 994 .MSTORE,
   pushAt 995 1 31,
   opAt 996 .NOT,
   opAt 997 .ADD,
   pushAt 998 2 2080,
   opAt 999 (.Dup ⟨2, by decide⟩),
   opAt 1000 .GT,
   pushAt 1001 2 1376,
   opAt 1002 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
