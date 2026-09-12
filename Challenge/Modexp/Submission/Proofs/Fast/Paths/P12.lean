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
  [opAt 1430 .JUMPDEST,
   opAt 1431 (.Dup ⟨1, by decide⟩),
   opAt 1432 .MLOAD,
   opAt 1433 (.Dup ⟨3, by decide⟩),
   opAt 1434 .MLOAD,
   opAt 1435 (.Dup ⟨1, by decide⟩),
   opAt 1436 .ADD,
   opAt 1437 (.Swap ⟨0, by decide⟩),
   opAt 1438 (.Dup ⟨1, by decide⟩),
   opAt 1439 .LT,
   opAt 1440 (.Swap ⟨0, by decide⟩),
   opAt 1441 (.Dup ⟨5, by decide⟩),
   opAt 1442 .ADD,
   opAt 1443 (.Swap ⟨4, by decide⟩),
   opAt 1444 (.Dup ⟨5, by decide⟩),
   opAt 1445 .LT,
   opAt 1446 .OR,
   opAt 1447 (.Swap ⟨3, by decide⟩),
   opAt 1448 (.Dup ⟨1, by decide⟩),
   opAt 1449 .MSTORE,
   pushAt 1450 1 31,
   opAt 1451 .NOT,
   opAt 1452 .ADD,
   opAt 1453 (.Swap ⟨0, by decide⟩),
   pushAt 1454 1 31,
   opAt 1455 .NOT,
   opAt 1456 .ADD,
   opAt 1457 (.Swap ⟨0, by decide⟩),
   opAt 1458 (.Swap ⟨1, by decide⟩),
   pushAt 1459 1 31,
   opAt 1460 .NOT,
   opAt 1461 .ADD,
   opAt 1462 (.Swap ⟨1, by decide⟩),
   pushAt 1463 2 8224,
   opAt 1464 (.Dup ⟨1, by decide⟩),
   opAt 1465 .GT,
   pushAt 1466 2 1925,
   opAt 1467 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1468 .POP,
   opAt 1469 .POP,
   opAt 1470 .POP,
   pushAt 1471 2 8224,
   opAt 1472 .MSTORE,

   pushAt 1473 2 4653,
   opAt 1474 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
