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
  [opAt 1444 .POP,
   opAt 1445 .POP,
   opAt 1446 (.Swap ⟨1, by decide⟩),
   opAt 1447 .POP,
   opAt 1448 .POP,
   opAt 1449 (.Dup ⟨0, by decide⟩),
   pushAt 1450 2 2080,
   opAt 1451 .MLOAD,
   opAt 1452 .ADD,
   opAt 1453 (.Dup ⟨0, by decide⟩),
   pushAt 1454 2 2112,
   opAt 1455 .MSTORE,
   opAt 1456 .LT,
   pushAt 1457 2 2048,
   opAt 1458 .MLOAD,
   opAt 1459 .ADD,
   pushAt 1460 2 2080,
   opAt 1461 .MSTORE,
   pushAt 1462 1 31,
   opAt 1463 .NOT,
   opAt 1464 .ADD,
   opAt 1465 (.Dup ⟨2, by decide⟩),
   opAt 1466 (.Dup ⟨1, by decide⟩),
   opAt 1467 .GT,
   pushAt 1468 2 1788,
   opAt 1469 .JUMPI]

/-- Instructions 1672..1726, pc 2595..2346. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1470 .POP,
   opAt 1471 .POP,
   opAt 1472 .POP,
   pushAt 1473 2 4877,
   opAt 1474 .JUMP]

/-- Instructions 1600..1753, pc 2347..2376. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1475 .JUMPDEST,
   pushAt 1476 2 2688,
   opAt 1477 .MLOAD,
   opAt 1478 (.Dup ⟨0, by decide⟩),
   opAt 1479 (.Dup ⟨2, by decide⟩),
   opAt 1480 .ADD,
   pushAt 1481 1 32,
   opAt 1482 (.Swap ⟨0, by decide⟩),
   opAt 1483 .SUB,
   opAt 1484 (.Dup ⟨1, by decide⟩),
   opAt 1485 (.Dup ⟨4, by decide⟩),
   opAt 1486 .ADD,
   pushAt 1487 1 32,
   opAt 1488 (.Swap ⟨0, by decide⟩),
   opAt 1489 .SUB,
   opAt 1490 (.Swap ⟨2, by decide⟩),
   opAt 1491 .POP,
   opAt 1492 (.Swap ⟨2, by decide⟩),
   opAt 1493 .POP,
   opAt 1494 .POP,
   pushAt 1495 2 2784,
   opAt 1496 .MLOAD,
   pushAt 1497 0 0,
   opAt 1498 (.Swap ⟨2, by decide⟩),
   opAt 1499 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
