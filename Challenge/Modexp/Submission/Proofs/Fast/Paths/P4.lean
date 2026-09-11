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
  [pushAt 1136 2 3058,
   opAt 1137 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1138 .JUMPDEST,
   opAt 1139 (.Dup ⟨1, by decide⟩),
   opAt 1140 (.Dup ⟨1, by decide⟩),
   opAt 1141 .EQ,
   pushAt 1142 2 1597,
   opAt 1143 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1144 2 1554,
   pushAt 1145 2 1024,
   pushAt 1146 2 5120,
   pushAt 1147 2 1024,
   pushAt 1148 2 4053,
   opAt 1149 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1150 .JUMPDEST,
   opAt 1151 (.Dup ⟨0, by decide⟩),
   opAt 1152 (.Dup ⟨2, by decide⟩),
   opAt 1153 .SUB,
   pushAt 1154 1 5,
   opAt 1155 .SHL,
   opAt 1156 (.Dup ⟨5, by decide⟩),
   opAt 1157 .SUB,
   pushAt 1158 1 96,
   opAt 1159 .ADD,
   opAt 1160 .CALLDATALOAD,
   opAt 1161 (.Dup ⟨3, by decide⟩),
   pushAt 1162 2 3040,
   opAt 1163 .ADD,
   opAt 1164 .MSTORE,
   pushAt 1165 2 1589,
   pushAt 1166 2 1024,
   pushAt 1167 2 3072,
   pushAt 1168 2 1024,
   pushAt 1169 2 2056,
   opAt 1170 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1171 .JUMPDEST,
   pushAt 1172 1 1,
   opAt 1173 .ADD,
   pushAt 1174 2 1530,
   opAt 1175 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
