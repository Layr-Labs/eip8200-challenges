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
  [pushAt 1195 2 3606,
   opAt 1196 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1216 .JUMPDEST,
   opAt 1217 (.Dup ⟨1, by decide⟩),
   opAt 1218 (.Dup ⟨1, by decide⟩),
   opAt 1219 .EQ,
   opAt 1220 .JUMPDEST,
   pushAt 1221 2 1736,
   opAt 1222 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1223 2 1693,
   pushAt 1224 2 1024,
   pushAt 1225 2 5120,
   pushAt 1226 2 1024,
   pushAt 1227 2 1939,
   opAt 1228 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1229 .JUMPDEST,
   opAt 1230 (.Dup ⟨0, by decide⟩),
   opAt 1231 (.Dup ⟨2, by decide⟩),
   opAt 1232 .SUB,
   pushAt 1233 1 5,
   opAt 1234 .SHL,
   opAt 1235 (.Dup ⟨5, by decide⟩),
   opAt 1236 .SUB,
   pushAt 1237 1 96,
   opAt 1238 .ADD,
   opAt 1239 .CALLDATALOAD,
   opAt 1240 (.Dup ⟨3, by decide⟩),
   pushAt 1241 2 3040,
   opAt 1242 .ADD,
   opAt 1243 .MSTORE,
   pushAt 1244 2 1728,
   pushAt 1245 2 1024,
   pushAt 1246 2 3072,
   pushAt 1247 2 1024,
   pushAt 1248 2 2467,
   opAt 1249 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1250 .JUMPDEST,
   pushAt 1251 1 1,
   opAt 1252 .ADD,
   pushAt 1253 2 1668,
   opAt 1254 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
