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
  [opAt 1275 .POP,
   opAt 1276 .POP,
   opAt 1277 (.Dup ⟨0, by decide⟩),
   pushAt 1278 2 8224,
   opAt 1279 .MLOAD,
   opAt 1280 .ADD,
   opAt 1281 (.Dup ⟨0, by decide⟩),
   pushAt 1282 2 8224,
   opAt 1283 .MSTORE,
   opAt 1284 .LT,
   pushAt 1285 2 8192,
   opAt 1286 .MSTORE,
   pushAt 1287 2 9440,
   opAt 1288 .MLOAD,
   opAt 1289 .MLOAD,
   pushAt 1290 2 9376,
   opAt 1291 .MLOAD,
   opAt 1292 .MUL,
   opAt 1293 (.Dup ⟨0, by decide⟩),
   pushAt 1294 2 9408,
   opAt 1295 .MLOAD,
   opAt 1296 .MLOAD,
   opAt 1297 (.Dup ⟨1, by decide⟩),
   opAt 1298 (.Dup ⟨1, by decide⟩),
   opAt 1299 .MUL,
   opAt 1300 (.Swap ⟨1, by decide⟩),
   pushAt 1301 0 0,
   opAt 1302 .NOT,
   opAt 1303 (.Swap ⟨1, by decide⟩),
   opAt 1304 .MULMOD,
   opAt 1305 (.Dup ⟨1, by decide⟩),
   opAt 1306 (.Dup ⟨1, by decide⟩),
   opAt 1307 .LT,
   opAt 1308 (.Dup ⟨2, by decide⟩),
   opAt 1309 .ADD,
   opAt 1310 (.Swap ⟨0, by decide⟩),
   opAt 1311 .SUB,
   opAt 1312 (.Swap ⟨0, by decide⟩),
   pushAt 1313 0 0,
   opAt 1314 .LT,
   opAt 1315 .ADD,
   pushAt 1316 2 9440,
   opAt 1317 .MLOAD,
   pushAt 1318 1 32,
   opAt 1319 (.Swap ⟨0, by decide⟩),
   opAt 1320 .SUB,
   pushAt 1321 2 9408,
   opAt 1322 .MLOAD,
   pushAt 1323 1 32,
   opAt 1324 (.Swap ⟨0, by decide⟩),
   opAt 1325 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
