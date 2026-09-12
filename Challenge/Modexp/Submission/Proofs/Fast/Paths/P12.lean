import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1675..1730). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1675..1709, pc 2302..2675. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1467 .JUMPDEST,
   opAt 1468 (.Dup ⟨1, by decide⟩),
   opAt 1469 .MLOAD,
   opAt 1470 (.Dup ⟨3, by decide⟩),
   opAt 1471 .MLOAD,
   opAt 1472 (.Dup ⟨1, by decide⟩),
   opAt 1473 .ADD,
   opAt 1474 (.Swap ⟨0, by decide⟩),
   opAt 1475 (.Dup ⟨1, by decide⟩),
   opAt 1476 .LT,
   opAt 1477 (.Swap ⟨0, by decide⟩),
   opAt 1478 (.Dup ⟨5, by decide⟩),
   opAt 1479 .ADD,
   opAt 1480 (.Swap ⟨4, by decide⟩),
   opAt 1481 (.Dup ⟨5, by decide⟩),
   opAt 1482 .LT,
   opAt 1483 .OR,
   opAt 1484 (.Swap ⟨3, by decide⟩),
   opAt 1485 (.Dup ⟨1, by decide⟩),
   opAt 1486 .MSTORE,
   pushAt 1487 1 31,
   opAt 1488 .NOT,
   opAt 1489 .ADD,
   opAt 1490 (.Swap ⟨0, by decide⟩),
   pushAt 1491 1 31,
   opAt 1492 .NOT,
   opAt 1493 .ADD,
   opAt 1494 (.Swap ⟨0, by decide⟩),
   opAt 1495 (.Swap ⟨1, by decide⟩),
   pushAt 1496 1 31,
   opAt 1497 .NOT,
   opAt 1498 .ADD,
   opAt 1499 (.Swap ⟨1, by decide⟩),
   pushAt 1500 2 8224,
   opAt 1501 (.Dup ⟨1, by decide⟩),
   opAt 1502 .GT,
   pushAt 1503 2 1977,
   opAt 1504 .JUMPI]

/-- Instructions 1710..1666, pc 2676..2353. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1505 .POP,
   opAt 1506 .POP,
   opAt 1507 .POP,
   pushAt 1508 2 8224,
   opAt 1509 .MSTORE,

   pushAt 1510 2 4792,
   opAt 1511 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
