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
  [opAt 976 .JUMPDEST,
   pushAt 977 1 64,
   opAt 978 .CALLDATALOAD,
   opAt 979 (.Dup ⟨0, by decide⟩),
   pushAt 980 1 33,
   opAt 981 .GT,
   
   pushAt 982 3 1877,
   opAt 983 .JUMPI]

/-- Instructions 986..1002, pc 1327..1352. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 984 1 32,
   opAt 985 .CALLDATALOAD,
   pushAt 986 0 0,
   opAt 987 .CALLDATALOAD,
   opAt 988 (.Dup ⟨2, by decide⟩),
   pushAt 989 2 1024,
   opAt 990 .LT,
   opAt 991 (.Dup ⟨2, by decide⟩),
   pushAt 992 2 1024,
   opAt 993 .LT,
   opAt 994 .OR,
   opAt 995 (.Dup ⟨1, by decide⟩),
   pushAt 996 2 1024,
   opAt 997 .LT,
   opAt 998 .OR,
   pushAt 999 2 1883,
   opAt 1000 .JUMPI]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1001 (.Dup ⟨2, by decide⟩),
   pushAt 1002 1 31,
   opAt 1003 .ADD,
   pushAt 1004 1 5,
   opAt 1005 .SHR,
   opAt 1006 (.Dup ⟨0, by decide⟩),
   pushAt 1007 1 5,
   opAt 1008 .SHL,
   opAt 1009 (.Dup ⟨3, by decide⟩),
   opAt 1010 (.Dup ⟨3, by decide⟩),
   opAt 1011 .ADD,
   pushAt 1012 1 96,
   opAt 1013 .ADD,
   opAt 1014 (.Dup ⟨5, by decide⟩),
   opAt 1015 (.Dup ⟨2, by decide⟩),
   opAt 1016 .SUB,
   pushAt 1017 1 3,
   opAt 1018 .SHL,
   opAt 1019 (.Dup ⟨1, by decide⟩),
   opAt 1020 .CALLDATALOAD,
   opAt 1021 (.Swap ⟨0, by decide⟩),
   opAt 1022 .SHR,
   opAt 1023 .ISZERO,
   pushAt 1024 2 1891,
   opAt 1025 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
