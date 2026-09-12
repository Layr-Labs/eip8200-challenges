import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1626). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1594, pc 2179..2459. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1272 .POP,
   opAt 1273 .POP,
   opAt 1274 (.Swap ⟨1, by decide⟩),
   opAt 1275 .POP,
   opAt 1276 .POP,
   opAt 1277 (.Dup ⟨0, by decide⟩),
   pushAt 1278 2 8224,
   opAt 1279 .MLOAD,
   opAt 1280 .ADD,
   opAt 1281 (.Dup ⟨0, by decide⟩),
   pushAt 1282 2 8256,
   opAt 1283 .MSTORE,
   opAt 1284 .LT,
   pushAt 1285 2 8192,
   opAt 1286 .MLOAD,
   opAt 1287 .ADD,
   pushAt 1288 2 8224,
   opAt 1289 .MSTORE,
   pushAt 1290 1 31,
   opAt 1291 .NOT,
   opAt 1292 .ADD,
   opAt 1293 (.Dup ⟨2, by decide⟩),
   opAt 1294 (.Dup ⟨1, by decide⟩),
   opAt 1295 .GT,
   pushAt 1296 2 1528,
   opAt 1297 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1298 .POP,
   opAt 1299 .POP,
   opAt 1300 .POP,
   pushAt 1301 2 4536,
   opAt 1302 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1303 .JUMPDEST,
   pushAt 1304 2 9344,
   opAt 1305 .MLOAD,
   opAt 1306 (.Dup ⟨0, by decide⟩),
   opAt 1307 (.Dup ⟨2, by decide⟩),
   opAt 1308 .ADD,
   pushAt 1309 1 32,
   opAt 1310 (.Swap ⟨0, by decide⟩),
   opAt 1311 .SUB,
   opAt 1312 (.Dup ⟨1, by decide⟩),
   opAt 1313 (.Dup ⟨4, by decide⟩),
   opAt 1314 .ADD,
   pushAt 1315 1 32,
   opAt 1316 (.Swap ⟨0, by decide⟩),
   opAt 1317 .SUB,
   opAt 1318 (.Swap ⟨2, by decide⟩),
   opAt 1319 .POP,
   opAt 1320 (.Swap ⟨2, by decide⟩),
   opAt 1321 .POP,
   opAt 1322 .POP,
   pushAt 1323 2 9440,
   opAt 1324 .MLOAD,
   pushAt 1325 0 0,
   opAt 1326 (.Swap ⟨2, by decide⟩),
   opAt 1327 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
