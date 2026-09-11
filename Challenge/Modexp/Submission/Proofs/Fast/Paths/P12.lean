import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1627..1682). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1627..1661, pc 2257..2634. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1456 .JUMPDEST,
   opAt 1457 (.Dup ⟨1, by decide⟩),
   opAt 1458 .MLOAD,
   opAt 1459 (.Dup ⟨3, by decide⟩),
   opAt 1460 .MLOAD,
   opAt 1461 (.Dup ⟨1, by decide⟩),
   opAt 1462 .ADD,
   opAt 1463 (.Swap ⟨0, by decide⟩),
   opAt 1464 (.Dup ⟨1, by decide⟩),
   opAt 1465 .LT,
   opAt 1466 (.Swap ⟨0, by decide⟩),
   opAt 1467 (.Dup ⟨5, by decide⟩),
   opAt 1468 .ADD,
   opAt 1469 (.Swap ⟨4, by decide⟩),
   opAt 1470 (.Dup ⟨5, by decide⟩),
   opAt 1471 .LT,
   opAt 1472 .OR,
   opAt 1473 (.Swap ⟨3, by decide⟩),
   opAt 1474 (.Dup ⟨1, by decide⟩),
   opAt 1475 .MSTORE,
   pushAt 1476 1 31,
   opAt 1477 .NOT,
   opAt 1478 .ADD,
   opAt 1479 (.Swap ⟨0, by decide⟩),
   pushAt 1480 1 31,
   opAt 1481 .NOT,
   opAt 1482 .ADD,
   opAt 1483 (.Swap ⟨0, by decide⟩),
   opAt 1484 (.Swap ⟨1, by decide⟩),
   pushAt 1485 1 31,
   opAt 1486 .NOT,
   opAt 1487 .ADD,
   opAt 1488 (.Swap ⟨1, by decide⟩),
   pushAt 1489 2 8224,
   opAt 1490 (.Dup ⟨1, by decide⟩),
   opAt 1491 .GT,
   pushAt 1492 2 1970,
   opAt 1493 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1494 .POP,
   opAt 1495 .POP,
   opAt 1496 .POP,
   pushAt 1497 2 8224,
   opAt 1498 .MSTORE,

   pushAt 1499 2 4671,
   opAt 1500 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
