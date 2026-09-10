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
  [pushAt 1178 2 3146,
   opAt 1179 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1180 .JUMPDEST,
   opAt 1181 (.Dup ⟨1, by decide⟩),
   opAt 1182 (.Dup ⟨1, by decide⟩),
   opAt 1183 .EQ,
   pushAt 1184 2 1678,
   opAt 1185 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1186 2 1635,
   pushAt 1187 2 1024,
   pushAt 1188 2 5120,
   pushAt 1189 2 1024,
   pushAt 1190 2 4137,
   opAt 1191 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1192 .JUMPDEST,
   opAt 1193 (.Dup ⟨0, by decide⟩),
   opAt 1194 (.Dup ⟨2, by decide⟩),
   opAt 1195 .SUB,
   pushAt 1196 1 5,
   opAt 1197 .SHL,
   opAt 1198 (.Dup ⟨5, by decide⟩),
   opAt 1199 .SUB,
   pushAt 1200 1 96,
   opAt 1201 .ADD,
   opAt 1202 .CALLDATALOAD,
   opAt 1203 (.Dup ⟨3, by decide⟩),
   pushAt 1204 2 3040,
   opAt 1205 .ADD,
   opAt 1206 .MSTORE,
   pushAt 1207 2 1670,
   pushAt 1208 2 1024,
   pushAt 1209 2 3072,
   pushAt 1210 2 1024,
   pushAt 1211 2 2137,
   opAt 1212 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1213 .JUMPDEST,
   pushAt 1214 1 1,
   opAt 1215 .ADD,
   pushAt 1216 2 1611,
   opAt 1217 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
