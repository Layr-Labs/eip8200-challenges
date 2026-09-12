import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 4 (instructions 1195..1254). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1195..1196, pc 1639..1642: jump to the appended full-base
dispatcher. The remaining decoded instructions through index 1215 are
unreachable padding, preserving the old loop head at index 1216 / pc 1668. -/
def blk1195 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1048 2 2884,
   opAt 1049 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1050 .JUMPDEST,
   opAt 1051 (.Dup ⟨1, by decide⟩),
   opAt 1052 (.Dup ⟨1, by decide⟩),
   opAt 1053 .EQ,
   pushAt 1054 2 1462,
   opAt 1055 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1056 2 1419,
   pushAt 1057 2 1024,
   pushAt 1058 2 5120,
   pushAt 1059 2 1024,
   pushAt 1060 2 3871,
   opAt 1061 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1062 .JUMPDEST,
   opAt 1063 (.Dup ⟨0, by decide⟩),
   opAt 1064 (.Dup ⟨2, by decide⟩),
   opAt 1065 .SUB,
   pushAt 1066 1 5,
   opAt 1067 .SHL,
   opAt 1068 (.Dup ⟨5, by decide⟩),
   opAt 1069 .SUB,
   pushAt 1070 1 96,
   opAt 1071 .ADD,
   opAt 1072 .CALLDATALOAD,
   opAt 1073 (.Dup ⟨3, by decide⟩),
   pushAt 1074 2 3040,
   opAt 1075 .ADD,
   opAt 1076 .MSTORE,
   pushAt 1077 2 1454,
   pushAt 1078 2 1024,
   pushAt 1079 2 3072,
   pushAt 1080 2 1024,
   pushAt 1081 2 1910,
   opAt 1082 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1083 .JUMPDEST,
   pushAt 1084 1 1,
   opAt 1085 .ADD,
   pushAt 1086 2 1395,
   opAt 1087 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
