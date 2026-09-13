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
  [opAt 958 .JUMPDEST,
   opAt 959 (.Dup ⟨0, by decide⟩),
   opAt 960 .MLOAD,
   pushAt 961 0 0,
   opAt 962 .NOT,
   opAt 963 (.Dup ⟨5, by decide⟩),
   opAt 964 (.Dup ⟨2, by decide⟩),
   opAt 965 .MUL,
   opAt 966 (.Swap ⟨1, by decide⟩),
   opAt 967 (.Dup ⟨6, by decide⟩),
   opAt 968 .MULMOD,
   opAt 969 (.Dup ⟨1, by decide⟩),
   opAt 970 (.Dup ⟨1, by decide⟩),
   opAt 971 .LT,
   opAt 972 .SUB,
   opAt 973 (.Dup ⟨4, by decide⟩),
   opAt 974 (.Dup ⟨2, by decide⟩),
   opAt 975 .ADD,
   opAt 976 (.Dup ⟨0, by decide⟩),
   opAt 977 (.Swap ⟨5, by decide⟩),
   opAt 978 .GT,
   opAt 979 .SUB,
   opAt 980 .SUB,
   opAt 981 (.Dup ⟨3, by decide⟩),
   opAt 982 (.Dup ⟨3, by decide⟩),
   opAt 983 .MLOAD,
   opAt 984 .ADD,
   opAt 985 (.Dup ⟨0, by decide⟩),
   opAt 986 (.Swap ⟨4, by decide⟩),
   opAt 987 .GT,
   opAt 988 .ADD,
   opAt 989 (.Swap ⟨2, by decide⟩),
   pushAt 990 1 32,
   opAt 991 (.Dup ⟨3, by decide⟩),
   pushAt 992 1 31,
   opAt 993 .NOT,
   opAt 994 .ADD,
   opAt 995 (.Swap ⟨3, by decide⟩),
   opAt 996 .ADD,
   opAt 997 .MSTORE,
   pushAt 998 1 31,
   opAt 999 .NOT,
   opAt 1000 .ADD,
   pushAt 1001 2 2080,
   opAt 1002 (.Dup ⟨2, by decide⟩),
   opAt 1003 .GT,
   pushAt 1004 2 1392,
   opAt 1005 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
