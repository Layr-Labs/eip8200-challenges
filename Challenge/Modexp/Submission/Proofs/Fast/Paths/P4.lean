import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 4 (instructions 1243..1302). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1243..1244, pc 1687..1690: jump to the appended full-base
dispatcher. The remaining decoded instructions through index 1215 are
unreachable padding, preserving the old loop head at index 1216 / pc 1716. -/
def blk1195 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1078 2 2913,
   opAt 1079 .JUMP]

/-- Instructions 1216..1270, pc 1716..1724. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1080 .JUMPDEST,
   opAt 1081 (.Dup ⟨1, by decide⟩),
   opAt 1082 (.Dup ⟨1, by decide⟩),
   opAt 1083 .EQ,
   pushAt 1084 2 1498,
   opAt 1085 .JUMPI]

/-- Instructions 1271..1276, pc 1725..1740. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1086 2 1455,
   pushAt 1087 2 1024,
   pushAt 1088 2 5120,
   pushAt 1089 2 1024,
   pushAt 1090 2 4055,
   opAt 1091 .JUMP]

/-- Instructions 1277..1297, pc 1741..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1092 .JUMPDEST,
   opAt 1093 (.Dup ⟨0, by decide⟩),
   opAt 1094 (.Dup ⟨2, by decide⟩),
   opAt 1095 .SUB,
   pushAt 1096 1 5,
   opAt 1097 .SHL,
   opAt 1098 (.Dup ⟨5, by decide⟩),
   opAt 1099 .SUB,
   pushAt 1100 1 96,
   opAt 1101 .ADD,
   opAt 1102 .CALLDATALOAD,
   opAt 1103 (.Dup ⟨3, by decide⟩),
   pushAt 1104 2 3040,
   opAt 1105 .ADD,
   opAt 1106 .MSTORE,
   pushAt 1107 2 1490,
   pushAt 1108 2 1024,
   pushAt 1109 2 3072,
   pushAt 1110 2 1024,
   pushAt 1111 2 1946,
   opAt 1112 .JUMP]

/-- Instructions 1250..1302, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1113 .JUMPDEST,
   pushAt 1114 1 1,
   opAt 1115 .ADD,
   pushAt 1116 2 1431,
   opAt 1117 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
