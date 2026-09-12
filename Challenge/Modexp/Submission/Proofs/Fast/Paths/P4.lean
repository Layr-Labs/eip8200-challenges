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
  [pushAt 1119 2 3007,
   opAt 1120 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1121 .JUMPDEST,
   opAt 1122 (.Dup ⟨1, by decide⟩),
   opAt 1123 (.Dup ⟨1, by decide⟩),
   opAt 1124 .EQ,
   pushAt 1125 2 1585,
   opAt 1126 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1127 2 1542,
   pushAt 1128 2 256,
   pushAt 1129 2 1280,
   pushAt 1130 2 256,
   pushAt 1131 2 4047,
   opAt 1132 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1133 .JUMPDEST,
   opAt 1134 (.Dup ⟨0, by decide⟩),
   opAt 1135 (.Dup ⟨2, by decide⟩),
   opAt 1136 .SUB,
   pushAt 1137 1 5,
   opAt 1138 .SHL,
   opAt 1139 (.Dup ⟨5, by decide⟩),
   opAt 1140 .SUB,
   pushAt 1141 1 96,
   opAt 1142 .ADD,
   opAt 1143 .CALLDATALOAD,
   opAt 1144 (.Dup ⟨3, by decide⟩),
   pushAt 1145 2 736,
   opAt 1146 .ADD,
   opAt 1147 .MSTORE,
   pushAt 1148 2 1577,
   pushAt 1149 2 256,
   pushAt 1150 2 768,
   pushAt 1151 2 256,
   pushAt 1152 2 2033,
   opAt 1153 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1154 .JUMPDEST,
   pushAt 1155 1 1,
   opAt 1156 .ADD,
   pushAt 1157 2 1518,
   opAt 1158 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
