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
  [opAt 1352 .POP,
   opAt 1353 .POP,
   opAt 1354 (.Dup ⟨0, by decide⟩),
   pushAt 1355 2 8224,
   opAt 1356 .MLOAD,
   opAt 1357 .ADD,
   opAt 1358 (.Dup ⟨0, by decide⟩),
   pushAt 1359 2 8224,
   opAt 1360 .MSTORE,
   opAt 1361 .LT,
   pushAt 1362 2 8192,
   opAt 1363 .MSTORE,
   pushAt 1364 2 9440,
   opAt 1365 .MLOAD,
   opAt 1366 .MLOAD,
   pushAt 1367 2 9376,
   opAt 1368 .MLOAD,
   opAt 1369 .MUL,
   opAt 1370 (.Dup ⟨0, by decide⟩),
   pushAt 1371 2 9408,
   opAt 1372 .MLOAD,
   opAt 1373 .MLOAD,
   opAt 1374 (.Dup ⟨1, by decide⟩),
   opAt 1375 (.Dup ⟨1, by decide⟩),
   opAt 1376 .MUL,
   opAt 1377 (.Swap ⟨1, by decide⟩),
   pushAt 1378 0 0,
   opAt 1379 .NOT,
   opAt 1380 (.Swap ⟨1, by decide⟩),
   opAt 1381 .MULMOD,
   opAt 1382 (.Dup ⟨1, by decide⟩),
   opAt 1383 (.Dup ⟨1, by decide⟩),
   opAt 1384 .LT,
   opAt 1385 (.Dup ⟨2, by decide⟩),
   opAt 1386 .ADD,
   opAt 1387 (.Swap ⟨0, by decide⟩),
   opAt 1388 .SUB,
   opAt 1389 (.Swap ⟨0, by decide⟩),
   pushAt 1390 0 0,
   opAt 1391 .LT,
   opAt 1392 .ADD,
   pushAt 1393 2 9440,
   opAt 1394 .MLOAD,
   pushAt 1395 1 32,
   opAt 1396 (.Swap ⟨0, by decide⟩),
   opAt 1397 .SUB,
   pushAt 1398 2 9408,
   opAt 1399 .MLOAD,
   pushAt 1400 1 32,
   opAt 1401 (.Swap ⟨0, by decide⟩),
   opAt 1402 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
