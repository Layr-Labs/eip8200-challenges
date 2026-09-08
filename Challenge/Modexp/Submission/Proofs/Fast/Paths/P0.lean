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
  [opAt 973 .JUMPDEST,
   pushAt 974 1 64,
   opAt 975 .CALLDATALOAD,
   opAt 976 (.Dup ⟨0, by decide⟩),
   pushAt 977 1 33,
   opAt 978 .GT,
      pushAt 979 2 1862,
   opAt 980 .JUMPI]

/-- Instructions 986..1002, pc 1327..1352. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 981 1 32,
   opAt 982 .CALLDATALOAD,
   pushAt 983 0 0,
   opAt 984 .CALLDATALOAD,
   opAt 985 (.Dup ⟨2, by decide⟩),
   pushAt 986 2 1024,
   opAt 987 .LT,
   opAt 988 (.Dup ⟨2, by decide⟩),
   pushAt 989 2 1024,
   opAt 990 .LT,
   opAt 991 .OR,
   opAt 992 (.Dup ⟨1, by decide⟩),
   pushAt 993 2 1024,
   opAt 994 .LT,
   opAt 995 .OR,
   pushAt 996 2 1868,
   opAt 997 .JUMPI]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 998 (.Dup ⟨2, by decide⟩),
   pushAt 999 1 31,
   opAt 1000 .ADD,
   pushAt 1001 1 5,
   opAt 1002 .SHR,
   opAt 1003 (.Dup ⟨0, by decide⟩),
   pushAt 1004 1 5,
   opAt 1005 .SHL,
   opAt 1006 (.Dup ⟨3, by decide⟩),
   opAt 1007 (.Dup ⟨3, by decide⟩),
   opAt 1008 .ADD,
   pushAt 1009 1 96,
   opAt 1010 .ADD,
   opAt 1011 (.Dup ⟨5, by decide⟩),
   opAt 1012 (.Dup ⟨2, by decide⟩),
   opAt 1013 .SUB,
   pushAt 1014 1 3,
   opAt 1015 .SHL,
   opAt 1016 (.Dup ⟨1, by decide⟩),
   opAt 1017 .CALLDATALOAD,
   opAt 1018 (.Swap ⟨0, by decide⟩),
   opAt 1019 .SHR,
   opAt 1020 .ISZERO,
   pushAt 1021 2 1876,
   opAt 1022 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
