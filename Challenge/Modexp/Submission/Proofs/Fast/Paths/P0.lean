import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 0 (instructions 977..1027). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 977..985, pc 1314..1326. -/
def blk977 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 971 .JUMPDEST,
   pushAt 972 1 64,
   opAt 973 .CALLDATALOAD,
   opAt 974 (.Dup ⟨0, by decide⟩),
   pushAt 975 1 33,
   opAt 976 .GT,
   pushAt 977 2 1867,
   opAt 978 .JUMPI]

/-- Instructions 986..1002, pc 1327..1352. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 979 1 32,
   opAt 980 .CALLDATALOAD,
   pushAt 981 0 0,
   opAt 982 .CALLDATALOAD,
   opAt 983 (.Dup ⟨2, by decide⟩),
   pushAt 984 2 1024,
   opAt 985 .LT,
   opAt 986 (.Dup ⟨2, by decide⟩),
   pushAt 987 2 1024,
   opAt 988 .LT,
   opAt 989 .OR,
   opAt 990 (.Dup ⟨1, by decide⟩),
   pushAt 991 2 1024,
   opAt 992 .LT,
   opAt 993 .OR,
   pushAt 994 2 1873,
   opAt 995 .JUMPI]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 996 (.Dup ⟨2, by decide⟩),
   pushAt 997 1 31,
   opAt 998 .ADD,
   pushAt 999 1 5,
   opAt 1000 .SHR,
   opAt 1001 (.Dup ⟨0, by decide⟩),
   pushAt 1002 1 5,
   opAt 1003 .SHL,
   opAt 1004 (.Dup ⟨3, by decide⟩),
   opAt 1005 (.Dup ⟨3, by decide⟩),
   opAt 1006 .ADD,
   pushAt 1007 1 96,
   opAt 1008 .ADD,
   opAt 1009 (.Dup ⟨5, by decide⟩),
   opAt 1010 (.Dup ⟨2, by decide⟩),
   opAt 1011 .SUB,
   pushAt 1012 1 3,
   opAt 1013 .SHL,
   opAt 1014 (.Dup ⟨1, by decide⟩),
   opAt 1015 .CALLDATALOAD,
   opAt 1016 (.Swap ⟨0, by decide⟩),
   opAt 1017 .SHR,
   opAt 1018 .ISZERO,
   pushAt 1019 2 1881,
   opAt 1020 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
