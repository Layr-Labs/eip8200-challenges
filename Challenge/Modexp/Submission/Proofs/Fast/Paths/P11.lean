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
  [opAt 1443 .POP,
   opAt 1444 .POP,
   opAt 1445 (.Swap ⟨1, by decide⟩),
   opAt 1446 .POP,
   opAt 1447 .POP,
   opAt 1448 (.Dup ⟨0, by decide⟩),
   pushAt 1449 2 2080,
   opAt 1450 .MLOAD,
   opAt 1451 .ADD,
   opAt 1452 (.Dup ⟨0, by decide⟩),
   pushAt 1453 2 2112,
   opAt 1454 .MSTORE,
   opAt 1455 .LT,
   pushAt 1456 2 2048,
   opAt 1457 .MLOAD,
   opAt 1458 .ADD,
   pushAt 1459 2 2080,
   opAt 1460 .MSTORE,
   pushAt 1461 1 31,
   opAt 1462 .NOT,
   opAt 1463 .ADD,
   opAt 1464 (.Dup ⟨2, by decide⟩),
   opAt 1465 (.Dup ⟨1, by decide⟩),
   opAt 1466 .GT,
   pushAt 1467 2 1788,
   opAt 1468 .JUMPI]

/-- Instructions 1672..1726, pc 2595..2346. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1469 .POP,
   opAt 1470 .POP,
   opAt 1471 .POP,
   pushAt 1472 2 4877,
   opAt 1473 .JUMP]

/-- Instructions 1600..1753, pc 2347..2376. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1474 .JUMPDEST,
   pushAt 1475 2 2688,
   opAt 1476 .MLOAD,
   opAt 1477 (.Dup ⟨0, by decide⟩),
   opAt 1478 (.Dup ⟨2, by decide⟩),
   opAt 1479 .ADD,
   pushAt 1480 1 32,
   opAt 1481 (.Swap ⟨0, by decide⟩),
   opAt 1482 .SUB,
   opAt 1483 (.Dup ⟨1, by decide⟩),
   opAt 1484 (.Dup ⟨4, by decide⟩),
   opAt 1485 .ADD,
   pushAt 1486 1 32,
   opAt 1487 (.Swap ⟨0, by decide⟩),
   opAt 1488 .SUB,
   opAt 1489 (.Swap ⟨2, by decide⟩),
   opAt 1490 .POP,
   opAt 1491 (.Swap ⟨2, by decide⟩),
   opAt 1492 .POP,
   opAt 1493 .POP,
   pushAt 1494 2 2784,
   opAt 1495 .MLOAD,
   pushAt 1496 0 0,
   opAt 1497 (.Swap ⟨2, by decide⟩),
   opAt 1498 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
