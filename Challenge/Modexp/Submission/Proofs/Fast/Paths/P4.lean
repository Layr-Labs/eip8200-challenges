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
  [pushAt 1191 2 3329,
   opAt 1192 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1212 .JUMPDEST,
   opAt 1213 (.Dup ⟨1, by decide⟩),
   opAt 1214 (.Dup ⟨1, by decide⟩),
   opAt 1215 .EQ,
   opAt 1216 .JUMPDEST,
   pushAt 1217 2 1727,
   opAt 1218 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1219 2 1684,
   pushAt 1220 2 1024,
   pushAt 1221 2 5120,
   pushAt 1222 2 1024,
   pushAt 1223 2 4428,
   opAt 1224 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1225 .JUMPDEST,
   opAt 1226 (.Dup ⟨0, by decide⟩),
   opAt 1227 (.Dup ⟨2, by decide⟩),
   opAt 1228 .SUB,
   pushAt 1229 1 5,
   opAt 1230 .SHL,
   opAt 1231 (.Dup ⟨5, by decide⟩),
   opAt 1232 .SUB,
   pushAt 1233 1 96,
   opAt 1234 .ADD,
   opAt 1235 .CALLDATALOAD,
   opAt 1236 (.Dup ⟨3, by decide⟩),
   pushAt 1237 2 3040,
   opAt 1238 .ADD,
   opAt 1239 .MSTORE,
   pushAt 1240 2 1719,
   pushAt 1241 2 1024,
   pushAt 1242 2 3072,
   pushAt 1243 2 1024,
   pushAt 1244 2 2203,
   opAt 1245 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1246 .JUMPDEST,
   pushAt 1247 1 1,
   opAt 1248 .ADD,
   pushAt 1249 2 1659,
   opAt 1250 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
