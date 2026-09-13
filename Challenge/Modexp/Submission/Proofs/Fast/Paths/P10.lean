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
  [opAt 963 .JUMPDEST,
   opAt 964 (.Dup ⟨0, by decide⟩),
   opAt 965 .MLOAD,
   pushAt 966 0 0,
   opAt 967 .NOT,
   opAt 968 (.Dup ⟨5, by decide⟩),
   opAt 969 (.Dup ⟨2, by decide⟩),
   opAt 970 .MUL,
   opAt 971 (.Swap ⟨1, by decide⟩),
   opAt 972 (.Dup ⟨6, by decide⟩),
   opAt 973 .MULMOD,
   opAt 974 (.Dup ⟨1, by decide⟩),
   opAt 975 (.Dup ⟨1, by decide⟩),
   opAt 976 .LT,
   opAt 977 .SUB,
   opAt 978 (.Dup ⟨4, by decide⟩),
   opAt 979 (.Dup ⟨2, by decide⟩),
   opAt 980 .ADD,
   opAt 981 (.Dup ⟨0, by decide⟩),
   opAt 982 (.Swap ⟨5, by decide⟩),
   opAt 983 .GT,
   opAt 984 .SUB,
   opAt 985 .SUB,
   opAt 986 (.Dup ⟨3, by decide⟩),
   opAt 987 (.Dup ⟨3, by decide⟩),
   opAt 988 .MLOAD,
   opAt 989 .ADD,
   opAt 990 (.Dup ⟨0, by decide⟩),
   opAt 991 (.Swap ⟨4, by decide⟩),
   opAt 992 .GT,
   opAt 993 .ADD,
   opAt 994 (.Swap ⟨2, by decide⟩),
   pushAt 995 1 32,
   opAt 996 (.Dup ⟨3, by decide⟩),
   pushAt 997 1 31,
   opAt 998 .NOT,
   opAt 999 .ADD,
   opAt 1000 (.Swap ⟨3, by decide⟩),
   opAt 1001 .ADD,
   opAt 1002 .MSTORE,
   pushAt 1003 1 31,
   opAt 1004 .NOT,
   opAt 1005 .ADD,
   pushAt 1006 2 2080,
   opAt 1007 (.Dup ⟨2, by decide⟩),
   opAt 1008 .GT,
   pushAt 1009 2 1392,
   opAt 1010 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
