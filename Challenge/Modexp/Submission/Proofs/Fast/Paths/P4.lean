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
  [pushAt 1118 2 3007,
   opAt 1119 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1120 .JUMPDEST,
   opAt 1121 (.Dup ⟨1, by decide⟩),
   opAt 1122 (.Dup ⟨1, by decide⟩),
   opAt 1123 .EQ,
   pushAt 1124 2 1585,
   opAt 1125 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1126 2 1542,
   pushAt 1127 2 1024,
   pushAt 1128 2 5120,
   pushAt 1129 2 1024,
   pushAt 1130 2 4047,
   opAt 1131 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1132 .JUMPDEST,
   opAt 1133 (.Dup ⟨0, by decide⟩),
   opAt 1134 (.Dup ⟨2, by decide⟩),
   opAt 1135 .SUB,
   pushAt 1136 1 5,
   opAt 1137 .SHL,
   opAt 1138 (.Dup ⟨5, by decide⟩),
   opAt 1139 .SUB,
   pushAt 1140 1 96,
   opAt 1141 .ADD,
   opAt 1142 .CALLDATALOAD,
   opAt 1143 (.Dup ⟨3, by decide⟩),
   pushAt 1144 2 3040,
   opAt 1145 .ADD,
   opAt 1146 .MSTORE,
   pushAt 1147 2 1577,
   pushAt 1148 2 1024,
   pushAt 1149 2 3072,
   pushAt 1150 2 1024,
   pushAt 1151 2 2033,
   opAt 1152 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1153 .JUMPDEST,
   pushAt 1154 1 1,
   opAt 1155 .ADD,
   pushAt 1156 2 1518,
   opAt 1157 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
