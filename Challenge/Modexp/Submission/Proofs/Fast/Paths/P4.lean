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
  [pushAt 1061 2 2913,
   opAt 1062 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1063 .JUMPDEST,
   opAt 1064 (.Dup ⟨1, by decide⟩),
   opAt 1065 (.Dup ⟨1, by decide⟩),
   opAt 1066 .EQ,
   pushAt 1067 2 1483,
   opAt 1068 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1069 2 1440,
   pushAt 1070 2 1024,
   pushAt 1071 2 5120,
   pushAt 1072 2 1024,
   pushAt 1073 2 3920,
   opAt 1074 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1075 .JUMPDEST,
   opAt 1076 (.Dup ⟨0, by decide⟩),
   opAt 1077 (.Dup ⟨2, by decide⟩),
   opAt 1078 .SUB,
   pushAt 1079 1 5,
   opAt 1080 .SHL,
   opAt 1081 (.Dup ⟨5, by decide⟩),
   opAt 1082 .SUB,
   pushAt 1083 1 96,
   opAt 1084 .ADD,
   opAt 1085 .CALLDATALOAD,
   opAt 1086 (.Dup ⟨3, by decide⟩),
   pushAt 1087 2 3040,
   opAt 1088 .ADD,
   opAt 1089 .MSTORE,
   pushAt 1090 2 1475,
   pushAt 1091 2 1024,
   pushAt 1092 2 3072,
   pushAt 1093 2 1024,
   pushAt 1094 2 1939,
   opAt 1095 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1096 .JUMPDEST,
   pushAt 1097 1 1,
   opAt 1098 .ADD,
   pushAt 1099 2 1416,
   opAt 1100 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
