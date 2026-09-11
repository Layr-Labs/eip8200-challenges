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
  [opAt 1279 .JUMPDEST,
   pushAt 1280 1 1,
   opAt 1281 (.Swap ⟨0, by decide⟩),
   opAt 1282 .SUB,
   opAt 1283 (.Dup ⟨0, by decide⟩),
   pushAt 1284 2 1760,
   opAt 1285 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1286 .POP,
   opAt 1287 .POP,
   opAt 1288 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1289 .JUMPDEST,
   pushAt 1290 2 2784,
   opAt 1291 .MLOAD,
   opAt 1292 (.Dup ⟨0, by decide⟩),
   pushAt 1293 1 64,
   opAt 1294 .ADD,
   opAt 1295 .CALLDATASIZE,
   pushAt 1296 2 2048,
   opAt 1297 .CALLDATACOPY,
   opAt 1298 (.Dup ⟨0, by decide⟩),
   opAt 1299 (.Dup ⟨3, by decide⟩),
   opAt 1300 .ADD,
   pushAt 1301 1 32,
   opAt 1302 (.Swap ⟨0, by decide⟩),
   opAt 1303 .SUB,
   pushAt 1304 1 32,
   opAt 1305 (.Dup ⟨4, by decide⟩),
   opAt 1306 .SUB,
   opAt 1307 (.Swap ⟨3, by decide⟩),
   opAt 1308 .POP,
   opAt 1309 (.Swap ⟨0, by decide⟩),
   opAt 1310 .POP,
   pushAt 1311 1 32,
   opAt 1312 (.Dup ⟨2, by decide⟩),
   opAt 1313 .SUB,
   opAt 1314 (.Swap ⟨1, by decide⟩),
   opAt 1315 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1316 .JUMPDEST,
   opAt 1317 (.Dup ⟨0, by decide⟩),
   opAt 1318 .MLOAD,
   pushAt 1319 0 0,
   pushAt 1320 2 2880,
   opAt 1321 .MLOAD,
   opAt 1322 (.Dup ⟨4, by decide⟩),
   pushAt 1323 2 2784,
   opAt 1324 .MLOAD,
   opAt 1325 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
