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
  [opAt 1353 .POP,
   opAt 1354 .POP,
   opAt 1355 (.Dup ⟨0, by decide⟩),
   pushAt 1356 2 4128,
   opAt 1357 .MLOAD,
   opAt 1358 .ADD,
   opAt 1359 (.Dup ⟨0, by decide⟩),
   pushAt 1360 2 4128,
   opAt 1361 .MSTORE,
   opAt 1362 .LT,
   pushAt 1363 2 4096,
   opAt 1364 .MSTORE,
   pushAt 1365 2 5344,
   opAt 1366 .MLOAD,
   opAt 1367 .MLOAD,
   pushAt 1368 2 5280,
   opAt 1369 .MLOAD,
   opAt 1370 .MUL,
   opAt 1371 (.Dup ⟨0, by decide⟩),
   pushAt 1372 2 5312,
   opAt 1373 .MLOAD,
   opAt 1374 .MLOAD,
   opAt 1375 (.Dup ⟨1, by decide⟩),
   opAt 1376 (.Dup ⟨1, by decide⟩),
   opAt 1377 .MUL,
   opAt 1378 (.Swap ⟨1, by decide⟩),
   pushAt 1379 0 0,
   opAt 1380 .NOT,
   opAt 1381 (.Swap ⟨1, by decide⟩),
   opAt 1382 .MULMOD,
   opAt 1383 (.Dup ⟨1, by decide⟩),
   opAt 1384 (.Dup ⟨1, by decide⟩),
   opAt 1385 .LT,
   opAt 1386 (.Dup ⟨2, by decide⟩),
   opAt 1387 .ADD,
   opAt 1388 (.Swap ⟨0, by decide⟩),
   opAt 1389 .SUB,
   opAt 1390 (.Swap ⟨0, by decide⟩),
   pushAt 1391 0 0,
   opAt 1392 .LT,
   opAt 1393 .ADD,
   pushAt 1394 2 5344,
   opAt 1395 .MLOAD,
   pushAt 1396 1 32,
   opAt 1397 (.Swap ⟨0, by decide⟩),
   opAt 1398 .SUB,
   pushAt 1399 2 5312,
   opAt 1400 .MLOAD,
   pushAt 1401 1 32,
   opAt 1402 (.Swap ⟨0, by decide⟩),
   opAt 1403 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
