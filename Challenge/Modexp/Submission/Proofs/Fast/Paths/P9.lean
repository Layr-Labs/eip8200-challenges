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
  [opAt 1277 .POP,
   opAt 1278 .POP,
   opAt 1279 (.Dup ⟨0, by decide⟩),
   pushAt 1280 2 8224,
   opAt 1281 .MLOAD,
   opAt 1282 .ADD,
   opAt 1283 (.Dup ⟨0, by decide⟩),
   pushAt 1284 2 8224,
   opAt 1285 .MSTORE,
   opAt 1286 .LT,
   pushAt 1287 2 8192,
   opAt 1288 .MSTORE,
   pushAt 1289 2 9440,
   opAt 1290 .MLOAD,
   opAt 1291 .MLOAD,
   pushAt 1292 2 9376,
   opAt 1293 .MLOAD,
   opAt 1294 .MUL,
   opAt 1295 (.Dup ⟨0, by decide⟩),
   pushAt 1296 2 9408,
   opAt 1297 .MLOAD,
   opAt 1298 .MLOAD,
   opAt 1299 (.Dup ⟨1, by decide⟩),
   opAt 1300 (.Dup ⟨1, by decide⟩),
   opAt 1301 .MUL,
   opAt 1302 (.Swap ⟨1, by decide⟩),
   pushAt 1303 0 0,
   opAt 1304 .NOT,
   opAt 1305 (.Swap ⟨1, by decide⟩),
   opAt 1306 .MULMOD,
   opAt 1307 (.Dup ⟨1, by decide⟩),
   opAt 1308 (.Dup ⟨1, by decide⟩),
   opAt 1309 .LT,
   opAt 1310 (.Dup ⟨2, by decide⟩),
   opAt 1311 .ADD,
   opAt 1312 (.Swap ⟨0, by decide⟩),
   opAt 1313 .SUB,
   opAt 1314 (.Swap ⟨0, by decide⟩),
   pushAt 1315 0 0,
   opAt 1316 .LT,
   opAt 1317 .ADD,
   pushAt 1318 2 9440,
   opAt 1319 .MLOAD,
   pushAt 1320 1 32,
   opAt 1321 (.Swap ⟨0, by decide⟩),
   opAt 1322 .SUB,
   pushAt 1323 2 9408,
   opAt 1324 .MLOAD,
   pushAt 1325 1 32,
   opAt 1326 (.Swap ⟨0, by decide⟩),
   opAt 1327 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
