import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1451..1550). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1451..1505, pc 2056..2065. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1252 .JUMPDEST,
   pushAt 1253 1 1,
   opAt 1254 (.Swap ⟨0, by decide⟩),
   opAt 1255 .SUB,
   opAt 1256 (.Dup ⟨0, by decide⟩),
   pushAt 1257 2 1732,
   opAt 1258 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2068. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1259 .POP,
   opAt 1260 .POP,
   opAt 1261 .JUMP]

/-- Instructions 1509..1487, pc 2069..2103. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1262 .JUMPDEST,
   pushAt 1263 2 5248,
   opAt 1264 .MLOAD,
   opAt 1265 (.Dup ⟨0, by decide⟩),
   pushAt 1266 1 64,
   opAt 1267 .ADD,
   opAt 1268 .CALLDATASIZE,
   pushAt 1269 2 4096,
   opAt 1270 .CALLDATACOPY,
   opAt 1271 (.Dup ⟨0, by decide⟩),
   opAt 1272 (.Dup ⟨3, by decide⟩),
   opAt 1273 .ADD,
   pushAt 1274 1 32,
   opAt 1275 (.Swap ⟨0, by decide⟩),
   opAt 1276 .SUB,
   pushAt 1277 1 32,
   opAt 1278 (.Dup ⟨4, by decide⟩),
   opAt 1279 .SUB,
   opAt 1280 (.Swap ⟨3, by decide⟩),
   opAt 1281 .POP,
   opAt 1282 (.Swap ⟨0, by decide⟩),
   opAt 1283 .POP,
   pushAt 1284 1 32,
   opAt 1285 (.Dup ⟨2, by decide⟩),
   opAt 1286 .SUB,
   opAt 1287 (.Swap ⟨1, by decide⟩),
   opAt 1288 .POP]

/-- Instructions 1536..1550, pc 2104..2124. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1289 .JUMPDEST,
   opAt 1290 (.Dup ⟨0, by decide⟩),
   opAt 1291 .MLOAD,
   pushAt 1292 0 0,
   pushAt 1293 2 5344,
   opAt 1294 .MLOAD,
   opAt 1295 (.Dup ⟨4, by decide⟩),
   pushAt 1296 2 5248,
   opAt 1297 .MLOAD,
   opAt 1298 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
