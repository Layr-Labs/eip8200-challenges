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
  [opAt 1428 .JUMPDEST,
   opAt 1429 (.Dup ⟨0, by decide⟩),
   opAt 1430 .MLOAD,
   pushAt 1431 0 0,
   opAt 1432 .NOT,
   opAt 1433 (.Dup ⟨5, by decide⟩),
   opAt 1434 (.Dup ⟨2, by decide⟩),
   opAt 1435 .MUL,
   opAt 1436 (.Swap ⟨1, by decide⟩),
   opAt 1437 (.Dup ⟨6, by decide⟩),
   opAt 1438 .MULMOD,
   opAt 1439 (.Dup ⟨1, by decide⟩),
   opAt 1440 (.Dup ⟨1, by decide⟩),
   opAt 1441 .LT,
   opAt 1442 .SUB,
   opAt 1443 (.Dup ⟨4, by decide⟩),
   opAt 1444 (.Dup ⟨2, by decide⟩),
   opAt 1445 .ADD,
   opAt 1446 (.Dup ⟨0, by decide⟩),
   opAt 1447 (.Swap ⟨5, by decide⟩),
   opAt 1448 .GT,
   opAt 1449 .SUB,
   opAt 1450 .SUB,
   opAt 1451 (.Dup ⟨3, by decide⟩),
   opAt 1452 (.Dup ⟨3, by decide⟩),
   opAt 1453 .MLOAD,
   opAt 1454 .ADD,
   opAt 1455 (.Dup ⟨0, by decide⟩),
   opAt 1456 (.Swap ⟨4, by decide⟩),
   opAt 1457 .GT,
   opAt 1458 .ADD,
   opAt 1459 (.Swap ⟨2, by decide⟩),
   pushAt 1460 1 32,
   opAt 1461 (.Dup ⟨3, by decide⟩),
   pushAt 1462 1 31,
   opAt 1463 .NOT,
   opAt 1464 .ADD,
   opAt 1465 (.Swap ⟨3, by decide⟩),
   opAt 1466 .ADD,
   opAt 1467 .MSTORE,
   pushAt 1468 1 31,
   opAt 1469 .NOT,
   opAt 1470 .ADD,
   pushAt 1471 2 8224,
   opAt 1472 (.Dup ⟨2, by decide⟩),
   opAt 1473 .GT,
   pushAt 1474 2 1957,
   opAt 1475 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
