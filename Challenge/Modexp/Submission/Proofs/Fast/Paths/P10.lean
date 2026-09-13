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
  [opAt 956 .JUMPDEST,
   opAt 957 (.Dup ⟨0, by decide⟩),
   opAt 958 .MLOAD,
   pushAt 959 0 0,
   opAt 960 .NOT,
   opAt 961 (.Dup ⟨5, by decide⟩),
   opAt 962 (.Dup ⟨2, by decide⟩),
   opAt 963 .MUL,
   opAt 964 (.Swap ⟨1, by decide⟩),
   opAt 965 (.Dup ⟨6, by decide⟩),
   opAt 966 .MULMOD,
   opAt 967 (.Dup ⟨1, by decide⟩),
   opAt 968 (.Dup ⟨1, by decide⟩),
   opAt 969 .LT,
   opAt 970 .SUB,
   opAt 971 (.Dup ⟨4, by decide⟩),
   opAt 972 (.Dup ⟨2, by decide⟩),
   opAt 973 .ADD,
   opAt 974 (.Dup ⟨0, by decide⟩),
   opAt 975 (.Swap ⟨5, by decide⟩),
   opAt 976 .GT,
   opAt 977 .SUB,
   opAt 978 .SUB,
   opAt 979 (.Dup ⟨3, by decide⟩),
   opAt 980 (.Dup ⟨3, by decide⟩),
   opAt 981 .MLOAD,
   opAt 982 .ADD,
   opAt 983 (.Dup ⟨0, by decide⟩),
   opAt 984 (.Swap ⟨4, by decide⟩),
   opAt 985 .GT,
   opAt 986 .ADD,
   opAt 987 (.Swap ⟨2, by decide⟩),
   pushAt 988 1 32,
   opAt 989 (.Dup ⟨3, by decide⟩),
   pushAt 990 1 31,
   opAt 991 .NOT,
   opAt 992 .ADD,
   opAt 993 (.Swap ⟨3, by decide⟩),
   opAt 994 .ADD,
   opAt 995 .MSTORE,
   pushAt 996 1 31,
   opAt 997 .NOT,
   opAt 998 .ADD,
   pushAt 999 2 2080,
   opAt 1000 (.Dup ⟨2, by decide⟩),
   opAt 1001 .GT,
   pushAt 1002 2 1376,
   opAt 1003 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
