import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1519..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1519..1568, pc 2119..2178. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1470 .JUMPDEST,
   opAt 1471 (.Dup ⟨0, by decide⟩),
   opAt 1472 .MLOAD,
   pushAt 1473 0 0,
   opAt 1474 .NOT,
   opAt 1475 (.Dup ⟨5, by decide⟩),
   opAt 1476 (.Dup ⟨2, by decide⟩),
   opAt 1477 .MUL,
   opAt 1478 (.Swap ⟨1, by decide⟩),
   opAt 1479 (.Dup ⟨6, by decide⟩),
   opAt 1480 .MULMOD,
   opAt 1481 (.Dup ⟨1, by decide⟩),
   opAt 1482 (.Dup ⟨1, by decide⟩),
   opAt 1483 .LT,
   opAt 1484 .SUB,
   opAt 1485 (.Dup ⟨4, by decide⟩),
   opAt 1486 (.Dup ⟨2, by decide⟩),
   opAt 1487 .ADD,
   opAt 1488 (.Dup ⟨0, by decide⟩),
   opAt 1489 (.Swap ⟨5, by decide⟩),
   opAt 1490 .GT,
   opAt 1491 .SUB,
   opAt 1492 .SUB,
   opAt 1493 (.Dup ⟨3, by decide⟩),
   opAt 1494 (.Dup ⟨3, by decide⟩),
   opAt 1495 .MLOAD,
   opAt 1496 .ADD,
   opAt 1497 (.Dup ⟨0, by decide⟩),
   opAt 1498 (.Swap ⟨4, by decide⟩),
   opAt 1499 .GT,
   opAt 1500 .ADD,
   opAt 1501 (.Swap ⟨2, by decide⟩),
   pushAt 1502 1 32,
   opAt 1503 (.Dup ⟨3, by decide⟩),
   pushAt 1504 1 31,
   opAt 1505 .NOT,
   opAt 1506 .ADD,
   opAt 1507 (.Swap ⟨3, by decide⟩),
   opAt 1508 .ADD,
   opAt 1509 .MSTORE,
   pushAt 1510 1 31,
   opAt 1511 .NOT,
   opAt 1512 .ADD,
   pushAt 1513 2 8224,
   opAt 1514 (.Dup ⟨2, by decide⟩),
   opAt 1515 .GT,
   pushAt 1516 2 2038,
   opAt 1517 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
