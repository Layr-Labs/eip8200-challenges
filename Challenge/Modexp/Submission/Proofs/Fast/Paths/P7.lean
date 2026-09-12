import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1369..1420). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1369..1375, pc 1926..1935. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1254 .JUMPDEST,
   pushAt 1255 1 1,
   opAt 1256 (.Swap ⟨0, by decide⟩),
   opAt 1257 .SUB,
   opAt 1258 (.Dup ⟨0, by decide⟩),
   pushAt 1259 2 1737,
   opAt 1260 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1261 .POP,
   opAt 1262 .POP,
   opAt 1263 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1264 .JUMPDEST,
   pushAt 1265 2 9344,
   opAt 1266 .MLOAD,
   opAt 1267 (.Dup ⟨0, by decide⟩),
   pushAt 1268 1 64,
   opAt 1269 .ADD,
   opAt 1270 .CALLDATASIZE,
   pushAt 1271 2 8192,
   opAt 1272 .CALLDATACOPY,
   opAt 1273 (.Dup ⟨0, by decide⟩),
   opAt 1274 (.Dup ⟨3, by decide⟩),
   opAt 1275 .ADD,
   pushAt 1276 1 32,
   opAt 1277 (.Swap ⟨0, by decide⟩),
   opAt 1278 .SUB,
   pushAt 1279 1 32,
   opAt 1280 (.Dup ⟨4, by decide⟩),
   opAt 1281 .SUB,
   opAt 1282 (.Swap ⟨3, by decide⟩),
   opAt 1283 .POP,
   opAt 1284 (.Swap ⟨0, by decide⟩),
   opAt 1285 .POP,
   pushAt 1286 1 32,
   opAt 1287 (.Dup ⟨2, by decide⟩),
   opAt 1288 .SUB,
   opAt 1289 (.Swap ⟨1, by decide⟩),
   opAt 1290 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1291 .JUMPDEST,
   opAt 1292 (.Dup ⟨0, by decide⟩),
   opAt 1293 .MLOAD,
   pushAt 1294 0 0,
   pushAt 1295 2 9440,
   opAt 1296 .MLOAD,
   opAt 1297 (.Dup ⟨4, by decide⟩),
   pushAt 1298 2 9344,
   opAt 1299 .MLOAD,
   opAt 1300 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
