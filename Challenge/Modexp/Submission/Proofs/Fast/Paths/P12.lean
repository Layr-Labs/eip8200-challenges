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
  [opAt 1432 .JUMPDEST,
   opAt 1433 (.Dup ⟨1, by decide⟩),
   opAt 1434 .MLOAD,
   opAt 1435 (.Dup ⟨3, by decide⟩),
   opAt 1436 .MLOAD,
   opAt 1437 (.Dup ⟨1, by decide⟩),
   opAt 1438 .ADD,
   opAt 1439 (.Swap ⟨0, by decide⟩),
   opAt 1440 (.Dup ⟨1, by decide⟩),
   opAt 1441 .LT,
   opAt 1442 (.Swap ⟨0, by decide⟩),
   opAt 1443 (.Dup ⟨5, by decide⟩),
   opAt 1444 .ADD,
   opAt 1445 (.Swap ⟨4, by decide⟩),
   opAt 1446 (.Dup ⟨5, by decide⟩),
   opAt 1447 .LT,
   opAt 1448 .OR,
   opAt 1449 (.Swap ⟨3, by decide⟩),
   opAt 1450 (.Dup ⟨1, by decide⟩),
   opAt 1451 .MSTORE,
   pushAt 1452 1 31,
   opAt 1453 .NOT,
   opAt 1454 .ADD,
   opAt 1455 (.Swap ⟨0, by decide⟩),
   pushAt 1456 1 31,
   opAt 1457 .NOT,
   opAt 1458 .ADD,
   opAt 1459 (.Swap ⟨0, by decide⟩),
   opAt 1460 (.Swap ⟨1, by decide⟩),
   pushAt 1461 1 31,
   opAt 1462 .NOT,
   opAt 1463 .ADD,
   opAt 1464 (.Swap ⟨1, by decide⟩),
   pushAt 1465 2 2080,
   opAt 1466 (.Dup ⟨1, by decide⟩),
   opAt 1467 .GT,
   pushAt 1468 2 1929,
   opAt 1469 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1470 .POP,
   opAt 1471 .POP,
   opAt 1472 .POP,
   pushAt 1473 2 2080,
   opAt 1474 .MSTORE,

   pushAt 1475 2 4669,
   opAt 1476 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
