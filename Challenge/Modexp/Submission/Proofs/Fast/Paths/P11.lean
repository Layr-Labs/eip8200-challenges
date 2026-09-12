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
  [opAt 1374 .POP,
   opAt 1375 .POP,
   opAt 1376 (.Swap ⟨1, by decide⟩),
   opAt 1377 .POP,
   opAt 1378 .POP,
   opAt 1379 (.Dup ⟨0, by decide⟩),
   pushAt 1380 2 8224,
   opAt 1381 .MLOAD,
   opAt 1382 .ADD,
   opAt 1383 (.Dup ⟨0, by decide⟩),
   pushAt 1384 2 8256,
   opAt 1385 .MSTORE,
   opAt 1386 .LT,
   pushAt 1387 2 8192,
   opAt 1388 .MLOAD,
   opAt 1389 .ADD,
   pushAt 1390 2 8224,
   opAt 1391 .MSTORE,
   pushAt 1392 1 31,
   opAt 1393 .NOT,
   opAt 1394 .ADD,
   opAt 1395 (.Dup ⟨2, by decide⟩),
   opAt 1396 (.Dup ⟨1, by decide⟩),
   opAt 1397 .GT,
   pushAt 1398 2 1657,
   opAt 1399 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1400 .POP,
   opAt 1401 .POP,
   opAt 1402 .POP,
   pushAt 1403 2 4653,
   opAt 1404 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1405 .JUMPDEST,
   pushAt 1406 2 9344,
   opAt 1407 .MLOAD,
   opAt 1408 (.Dup ⟨0, by decide⟩),
   opAt 1409 (.Dup ⟨2, by decide⟩),
   opAt 1410 .ADD,
   pushAt 1411 1 32,
   opAt 1412 (.Swap ⟨0, by decide⟩),
   opAt 1413 .SUB,
   opAt 1414 (.Dup ⟨1, by decide⟩),
   opAt 1415 (.Dup ⟨4, by decide⟩),
   opAt 1416 .ADD,
   pushAt 1417 1 32,
   opAt 1418 (.Swap ⟨0, by decide⟩),
   opAt 1419 .SUB,
   opAt 1420 (.Swap ⟨2, by decide⟩),
   opAt 1421 .POP,
   opAt 1422 (.Swap ⟨2, by decide⟩),
   opAt 1423 .POP,
   opAt 1424 .POP,
   pushAt 1425 2 9440,
   opAt 1426 .MLOAD,
   pushAt 1427 0 0,
   opAt 1428 (.Swap ⟨2, by decide⟩),
   opAt 1429 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
