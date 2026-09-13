import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1753). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1721, pc 2304..2592. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1448 .POP,
   opAt 1449 .POP,
   opAt 1450 (.Swap ⟨1, by decide⟩),
   opAt 1451 .POP,
   opAt 1452 .POP,
   opAt 1453 (.Dup ⟨0, by decide⟩),
   pushAt 1454 2 2080,
   opAt 1455 .MLOAD,
   opAt 1456 .ADD,
   opAt 1457 (.Dup ⟨0, by decide⟩),
   pushAt 1458 2 2112,
   opAt 1459 .MSTORE,
   opAt 1460 .LT,
   pushAt 1461 2 2048,
   opAt 1462 .MLOAD,
   opAt 1463 .ADD,
   pushAt 1464 2 2080,
   opAt 1465 .MSTORE,
   pushAt 1466 1 31,
   opAt 1467 .NOT,
   opAt 1468 .ADD,
   opAt 1469 (.Dup ⟨2, by decide⟩),
   opAt 1470 (.Dup ⟨1, by decide⟩),
   opAt 1471 .GT,
   pushAt 1472 2 1788,
   opAt 1473 .JUMPI]

/-- Instructions 1672..1726, pc 2595..2346. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1474 .POP,
   opAt 1475 .POP,
   opAt 1476 .POP,
   pushAt 1477 2 4877,
   opAt 1478 .JUMP]

/-- Instructions 1600..1753, pc 2347..2376. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1479 .JUMPDEST,
   pushAt 1480 2 2688,
   opAt 1481 .MLOAD,
   opAt 1482 (.Dup ⟨0, by decide⟩),
   opAt 1483 (.Dup ⟨2, by decide⟩),
   opAt 1484 .ADD,
   pushAt 1485 1 32,
   opAt 1486 (.Swap ⟨0, by decide⟩),
   opAt 1487 .SUB,
   opAt 1488 (.Dup ⟨1, by decide⟩),
   opAt 1489 (.Dup ⟨4, by decide⟩),
   opAt 1490 .ADD,
   pushAt 1491 1 32,
   opAt 1492 (.Swap ⟨0, by decide⟩),
   opAt 1493 .SUB,
   opAt 1494 (.Swap ⟨2, by decide⟩),
   opAt 1495 .POP,
   opAt 1496 (.Swap ⟨2, by decide⟩),
   opAt 1497 .POP,
   opAt 1498 .POP,
   pushAt 1499 2 2784,
   opAt 1500 .MLOAD,
   pushAt 1501 0 0,
   opAt 1502 (.Swap ⟨2, by decide⟩),
   opAt 1503 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
