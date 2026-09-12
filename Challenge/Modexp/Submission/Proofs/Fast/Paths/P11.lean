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
  [opAt 1381 .POP,
   opAt 1382 .POP,
   opAt 1383 (.Swap ⟨1, by decide⟩),
   opAt 1384 .POP,
   opAt 1385 .POP,
   opAt 1386 (.Dup ⟨0, by decide⟩),
   pushAt 1387 2 8224,
   opAt 1388 .MLOAD,
   opAt 1389 .ADD,
   opAt 1390 (.Dup ⟨0, by decide⟩),
   pushAt 1391 2 8256,
   opAt 1392 .MSTORE,
   opAt 1393 .LT,
   pushAt 1394 2 8192,
   opAt 1395 .MLOAD,
   opAt 1396 .ADD,
   pushAt 1397 2 8224,
   opAt 1398 .MSTORE,
   pushAt 1399 1 31,
   opAt 1400 .NOT,
   opAt 1401 .ADD,
   opAt 1402 (.Dup ⟨2, by decide⟩),
   opAt 1403 (.Dup ⟨1, by decide⟩),
   opAt 1404 .GT,
   pushAt 1405 2 1673,
   opAt 1406 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1407 .POP,
   opAt 1408 .POP,
   opAt 1409 .POP,
   pushAt 1410 2 4642,
   opAt 1411 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1412 .JUMPDEST,
   pushAt 1413 2 9344,
   opAt 1414 .MLOAD,
   opAt 1415 (.Dup ⟨0, by decide⟩),
   opAt 1416 (.Dup ⟨2, by decide⟩),
   opAt 1417 .ADD,
   pushAt 1418 1 32,
   opAt 1419 (.Swap ⟨0, by decide⟩),
   opAt 1420 .SUB,
   opAt 1421 (.Dup ⟨1, by decide⟩),
   opAt 1422 (.Dup ⟨4, by decide⟩),
   opAt 1423 .ADD,
   pushAt 1424 1 32,
   opAt 1425 (.Swap ⟨0, by decide⟩),
   opAt 1426 .SUB,
   opAt 1427 (.Swap ⟨2, by decide⟩),
   opAt 1428 .POP,
   opAt 1429 (.Swap ⟨2, by decide⟩),
   opAt 1430 .POP,
   opAt 1431 .POP,
   pushAt 1432 2 9440,
   opAt 1433 .MLOAD,
   pushAt 1434 0 0,
   opAt 1435 (.Swap ⟨2, by decide⟩),
   opAt 1436 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
