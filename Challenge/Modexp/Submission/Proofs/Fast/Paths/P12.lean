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
  [opAt 1437 .JUMPDEST,
   opAt 1438 (.Dup ⟨1, by decide⟩),
   opAt 1439 .MLOAD,
   opAt 1440 (.Dup ⟨3, by decide⟩),
   opAt 1441 .MLOAD,
   opAt 1442 (.Dup ⟨1, by decide⟩),
   opAt 1443 .ADD,
   opAt 1444 (.Swap ⟨0, by decide⟩),
   opAt 1445 (.Dup ⟨1, by decide⟩),
   opAt 1446 .LT,
   opAt 1447 (.Swap ⟨0, by decide⟩),
   opAt 1448 (.Dup ⟨5, by decide⟩),
   opAt 1449 .ADD,
   opAt 1450 (.Swap ⟨4, by decide⟩),
   opAt 1451 (.Dup ⟨5, by decide⟩),
   opAt 1452 .LT,
   opAt 1453 .OR,
   opAt 1454 (.Swap ⟨3, by decide⟩),
   opAt 1455 (.Dup ⟨1, by decide⟩),
   opAt 1456 .MSTORE,
   pushAt 1457 1 31,
   opAt 1458 .NOT,
   opAt 1459 .ADD,
   opAt 1460 (.Swap ⟨0, by decide⟩),
   pushAt 1461 1 31,
   opAt 1462 .NOT,
   opAt 1463 .ADD,
   opAt 1464 (.Swap ⟨0, by decide⟩),
   opAt 1465 (.Swap ⟨1, by decide⟩),
   pushAt 1466 1 31,
   opAt 1467 .NOT,
   opAt 1468 .ADD,
   opAt 1469 (.Swap ⟨1, by decide⟩),
   pushAt 1470 2 8224,
   opAt 1471 (.Dup ⟨1, by decide⟩),
   opAt 1472 .GT,
   pushAt 1473 2 1941,
   opAt 1474 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1475 .POP,
   opAt 1476 .POP,
   opAt 1477 .POP,
   pushAt 1478 2 8224,
   opAt 1479 .MSTORE,

   pushAt 1480 2 4642,
   opAt 1481 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
