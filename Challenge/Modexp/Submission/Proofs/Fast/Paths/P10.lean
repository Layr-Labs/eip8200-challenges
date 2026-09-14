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
  [opAt 957 .JUMPDEST,
   opAt 958 (.Dup ⟨0, by decide⟩),
   opAt 959 .MLOAD,
   pushAt 960 0 0,
   opAt 961 .NOT,
   opAt 962 (.Dup ⟨5, by decide⟩),
   opAt 963 (.Dup ⟨2, by decide⟩),
   opAt 964 .MUL,
   opAt 965 (.Swap ⟨1, by decide⟩),
   opAt 966 (.Dup ⟨6, by decide⟩),
   opAt 967 .MULMOD,
   opAt 968 (.Dup ⟨1, by decide⟩),
   opAt 969 (.Dup ⟨1, by decide⟩),
   opAt 970 .LT,
   opAt 971 .SUB,
   opAt 972 (.Dup ⟨4, by decide⟩),
   opAt 973 (.Dup ⟨2, by decide⟩),
   opAt 974 .ADD,
   opAt 975 (.Dup ⟨0, by decide⟩),
   opAt 976 (.Swap ⟨5, by decide⟩),
   opAt 977 .GT,
   opAt 978 .SUB,
   opAt 979 .SUB,
   opAt 980 (.Dup ⟨3, by decide⟩),
   opAt 981 (.Dup ⟨3, by decide⟩),
   opAt 982 .MLOAD,
   opAt 983 .ADD,
   opAt 984 (.Dup ⟨0, by decide⟩),
   opAt 985 (.Swap ⟨4, by decide⟩),
   opAt 986 .GT,
   opAt 987 .ADD,
   opAt 988 (.Swap ⟨2, by decide⟩),
   pushAt 989 1 32,
   opAt 990 (.Dup ⟨3, by decide⟩),
   pushAt 991 1 31,
   opAt 992 .NOT,
   opAt 993 .ADD,
   opAt 994 (.Swap ⟨3, by decide⟩),
   opAt 995 .ADD,
   opAt 996 .MSTORE,
   pushAt 997 1 31,
   opAt 998 .NOT,
   opAt 999 .ADD,
   pushAt 1000 2 2080,
   opAt 1001 (.Dup ⟨2, by decide⟩),
   opAt 1002 .GT,
   pushAt 1003 2 1376,
   opAt 1004 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
