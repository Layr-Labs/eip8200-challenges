import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1469..1518). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1469..1518, pc 2050..2118. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1282 .POP,
   opAt 1283 .POP,
   opAt 1284 (.Dup ⟨0, by decide⟩),
   pushAt 1285 2 8224,
   opAt 1286 .MLOAD,
   opAt 1287 .ADD,
   opAt 1288 (.Dup ⟨0, by decide⟩),
   pushAt 1289 2 8224,
   opAt 1290 .MSTORE,
   opAt 1291 .LT,
   pushAt 1292 2 8192,
   opAt 1293 .MSTORE,
   pushAt 1294 2 9440,
   opAt 1295 .MLOAD,
   opAt 1296 .MLOAD,
   pushAt 1297 2 9376,
   opAt 1298 .MLOAD,
   opAt 1299 .MUL,
   opAt 1300 (.Dup ⟨0, by decide⟩),
   pushAt 1301 2 9408,
   opAt 1302 .MLOAD,
   opAt 1303 .MLOAD,
   opAt 1304 (.Dup ⟨1, by decide⟩),
   opAt 1305 (.Dup ⟨1, by decide⟩),
   opAt 1306 .MUL,
   opAt 1307 (.Swap ⟨1, by decide⟩),
   pushAt 1308 0 0,
   opAt 1309 .NOT,
   opAt 1310 (.Swap ⟨1, by decide⟩),
   opAt 1311 .MULMOD,
   opAt 1312 (.Dup ⟨1, by decide⟩),
   opAt 1313 (.Dup ⟨1, by decide⟩),
   opAt 1314 .LT,
   opAt 1315 (.Dup ⟨2, by decide⟩),
   opAt 1316 .ADD,
   opAt 1317 (.Swap ⟨0, by decide⟩),
   opAt 1318 .SUB,
   opAt 1319 (.Swap ⟨0, by decide⟩),
   pushAt 1320 0 0,
   opAt 1321 .LT,
   opAt 1322 .ADD,
   pushAt 1323 2 9440,
   opAt 1324 .MLOAD,
   pushAt 1325 1 32,
   opAt 1326 (.Swap ⟨0, by decide⟩),
   opAt 1327 .SUB,
   pushAt 1328 2 9408,
   opAt 1329 .MLOAD,
   pushAt 1330 1 32,
   opAt 1331 (.Swap ⟨0, by decide⟩),
   opAt 1332 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
