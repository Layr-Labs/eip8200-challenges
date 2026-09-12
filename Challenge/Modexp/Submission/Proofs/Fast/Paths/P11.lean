import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1674). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1642, pc 2227..2500. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1411 .POP,
   opAt 1412 .POP,
   opAt 1413 (.Swap ⟨1, by decide⟩),
   opAt 1414 .POP,
   opAt 1415 .POP,
   opAt 1416 (.Dup ⟨0, by decide⟩),
   pushAt 1417 2 8224,
   opAt 1418 .MLOAD,
   opAt 1419 .ADD,
   opAt 1420 (.Dup ⟨0, by decide⟩),
   pushAt 1421 2 8256,
   opAt 1422 .MSTORE,
   opAt 1423 .LT,
   pushAt 1424 2 8192,
   opAt 1425 .MLOAD,
   opAt 1426 .ADD,
   pushAt 1427 2 8224,
   opAt 1428 .MSTORE,
   pushAt 1429 1 31,
   opAt 1430 .NOT,
   opAt 1431 .ADD,
   opAt 1432 (.Dup ⟨2, by decide⟩),
   opAt 1433 (.Dup ⟨1, by decide⟩),
   opAt 1434 .GT,
   pushAt 1435 2 1709,
   opAt 1436 .JUMPI]

/-- Instructions 1595..1647, pc 2501..2268. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1437 .POP,
   opAt 1438 .POP,
   opAt 1439 .POP,
   pushAt 1440 2 4792,
   opAt 1441 .JUMP]

/-- Instructions 1600..1674, pc 2269..2301. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1442 .JUMPDEST,
   pushAt 1443 2 9344,
   opAt 1444 .MLOAD,
   opAt 1445 (.Dup ⟨0, by decide⟩),
   opAt 1446 (.Dup ⟨2, by decide⟩),
   opAt 1447 .ADD,
   pushAt 1448 1 32,
   opAt 1449 (.Swap ⟨0, by decide⟩),
   opAt 1450 .SUB,
   opAt 1451 (.Dup ⟨1, by decide⟩),
   opAt 1452 (.Dup ⟨4, by decide⟩),
   opAt 1453 .ADD,
   pushAt 1454 1 32,
   opAt 1455 (.Swap ⟨0, by decide⟩),
   opAt 1456 .SUB,
   opAt 1457 (.Swap ⟨2, by decide⟩),
   opAt 1458 .POP,
   opAt 1459 (.Swap ⟨2, by decide⟩),
   opAt 1460 .POP,
   opAt 1461 .POP,
   pushAt 1462 2 9440,
   opAt 1463 .MLOAD,
   pushAt 1464 0 0,
   opAt 1465 (.Swap ⟨2, by decide⟩),
   opAt 1466 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
