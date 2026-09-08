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
  [opAt 972 .JUMPDEST,
   pushAt 973 1 64,
   opAt 974 .CALLDATALOAD,
   opAt 975 (.Dup ⟨0, by decide⟩),
   pushAt 976 1 33,
   opAt 977 .GT,
      pushAt 978 2 1855,
   opAt 979 .JUMPI]

/-- Instructions 986..1002, pc 1327..1352. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 980 1 32,
   opAt 981 .CALLDATALOAD,
   pushAt 982 0 0,
   opAt 983 .CALLDATALOAD,
   opAt 984 (.Dup ⟨2, by decide⟩),
   pushAt 985 2 1024,
   opAt 986 .LT,
   opAt 987 (.Dup ⟨2, by decide⟩),
   pushAt 988 2 1024,
   opAt 989 .LT,
   opAt 990 .OR,
   opAt 991 (.Dup ⟨1, by decide⟩),
   pushAt 992 2 1024,
   opAt 993 .LT,
   opAt 994 .OR,
   pushAt 995 2 1861,
   opAt 996 .JUMPI]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 997 (.Dup ⟨2, by decide⟩),
   pushAt 998 1 31,
   opAt 999 .ADD,
   pushAt 1000 1 5,
   opAt 1001 .SHR,
   opAt 1002 (.Dup ⟨0, by decide⟩),
   pushAt 1003 1 5,
   opAt 1004 .SHL,
   opAt 1005 (.Dup ⟨3, by decide⟩),
   opAt 1006 (.Dup ⟨3, by decide⟩),
   opAt 1007 .ADD,
   pushAt 1008 1 96,
   opAt 1009 .ADD,
   opAt 1010 (.Dup ⟨5, by decide⟩),
   opAt 1011 (.Dup ⟨2, by decide⟩),
   opAt 1012 .SUB,
   pushAt 1013 1 3,
   opAt 1014 .SHL,
   opAt 1015 (.Dup ⟨1, by decide⟩),
   opAt 1016 .CALLDATALOAD,
   opAt 1017 (.Swap ⟨0, by decide⟩),
   opAt 1018 .SHR,
   opAt 1019 .ISZERO,
   pushAt 1020 2 1869,
   opAt 1021 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
