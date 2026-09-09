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
  [pushAt 1189 2 3329,
   opAt 1190 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1210 .JUMPDEST,
   opAt 1211 (.Dup ⟨1, by decide⟩),
   opAt 1212 (.Dup ⟨1, by decide⟩),
   opAt 1213 .EQ,
   opAt 1214 .JUMPDEST,
   pushAt 1215 2 1727,
   opAt 1216 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1217 2 1684,
   pushAt 1218 2 1024,
   pushAt 1219 2 5120,
   pushAt 1220 2 1024,
   pushAt 1221 2 4424,
   opAt 1222 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1223 .JUMPDEST,
   opAt 1224 (.Dup ⟨0, by decide⟩),
   opAt 1225 (.Dup ⟨2, by decide⟩),
   opAt 1226 .SUB,
   pushAt 1227 1 5,
   opAt 1228 .SHL,
   opAt 1229 (.Dup ⟨5, by decide⟩),
   opAt 1230 .SUB,
   pushAt 1231 1 96,
   opAt 1232 .ADD,
   opAt 1233 .CALLDATALOAD,
   opAt 1234 (.Dup ⟨3, by decide⟩),
   pushAt 1235 2 3040,
   opAt 1236 .ADD,
   opAt 1237 .MSTORE,
   pushAt 1238 2 1719,
   pushAt 1239 2 1024,
   pushAt 1240 2 3072,
   pushAt 1241 2 1024,
   pushAt 1242 2 2203,
   opAt 1243 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1244 .JUMPDEST,
   pushAt 1245 1 1,
   opAt 1246 .ADD,
   pushAt 1247 2 1659,
   opAt 1248 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
