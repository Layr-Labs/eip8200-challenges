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
  [opAt 977 .JUMPDEST,
   pushAt 978 1 64,
   opAt 979 .CALLDATALOAD,
   opAt 980 (.Dup ⟨0, by decide⟩),
   pushAt 981 1 33,
   opAt 982 .GT,
   pushAt 983 2 1812,
   opAt 984 .JUMPI]

/-- Instructions 986..1002, pc 1327..1352. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 985 1 32,
   opAt 986 .CALLDATALOAD,
   pushAt 987 0 0,
   opAt 988 .CALLDATALOAD,
   opAt 989 (.Dup ⟨2, by decide⟩),
   pushAt 990 2 1024,
   opAt 991 .LT,
   opAt 992 (.Dup ⟨2, by decide⟩),
   pushAt 993 2 1024,
   opAt 994 .LT,
   opAt 995 .OR,
   opAt 996 (.Dup ⟨1, by decide⟩),
   pushAt 997 2 1024,
   opAt 998 .LT,
   opAt 999 .OR,
   pushAt 1000 2 1818,
   opAt 1001 .JUMPI]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1002 (.Dup ⟨2, by decide⟩),
   pushAt 1003 1 31,
   opAt 1004 .ADD,
   pushAt 1005 1 5,
   opAt 1006 .SHR,
   opAt 1007 (.Dup ⟨0, by decide⟩),
   pushAt 1008 1 5,
   opAt 1009 .SHL,
   opAt 1010 (.Dup ⟨3, by decide⟩),
   opAt 1011 (.Dup ⟨3, by decide⟩),
   opAt 1012 .ADD,
   pushAt 1013 1 96,
   opAt 1014 .ADD,
   opAt 1015 (.Dup ⟨5, by decide⟩),
   opAt 1016 (.Dup ⟨2, by decide⟩),
   opAt 1017 .SUB,
   pushAt 1018 1 3,
   opAt 1019 .SHL,
   opAt 1020 (.Dup ⟨1, by decide⟩),
   opAt 1021 .CALLDATALOAD,
   opAt 1022 (.Swap ⟨0, by decide⟩),
   opAt 1023 .SHR,
   opAt 1024 .ISZERO,
   pushAt 1025 2 1826,
   opAt 1026 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
