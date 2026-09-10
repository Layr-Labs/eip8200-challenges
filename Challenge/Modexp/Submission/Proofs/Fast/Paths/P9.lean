import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1469..1518). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1469..1518, pc 2050..2118. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1419 .POP,
   opAt 1420 .POP,
   opAt 1421 (.Dup ⟨0, by decide⟩),
   pushAt 1422 2 8224,
   opAt 1423 .MLOAD,
   opAt 1424 .ADD,
   opAt 1425 (.Dup ⟨0, by decide⟩),
   pushAt 1426 2 8224,
   opAt 1427 .MSTORE,
   opAt 1428 .LT,
   pushAt 1429 2 8192,
   opAt 1430 .MSTORE,
   pushAt 1431 2 9440,
   opAt 1432 .MLOAD,
   opAt 1433 .MLOAD,
   pushAt 1434 2 9376,
   opAt 1435 .MLOAD,
   opAt 1436 .MUL,
   opAt 1437 (.Dup ⟨0, by decide⟩),
   pushAt 1438 2 9408,
   opAt 1439 .MLOAD,
   opAt 1440 .MLOAD,
   opAt 1441 (.Dup ⟨1, by decide⟩),
   opAt 1442 (.Dup ⟨1, by decide⟩),
   opAt 1443 .MUL,
   opAt 1444 (.Swap ⟨1, by decide⟩),
   pushAt 1445 0 0,
   opAt 1446 .NOT,
   opAt 1447 (.Swap ⟨1, by decide⟩),
   opAt 1448 .MULMOD,
   opAt 1449 (.Dup ⟨1, by decide⟩),
   opAt 1450 (.Dup ⟨1, by decide⟩),
   opAt 1451 .LT,
   opAt 1452 (.Dup ⟨2, by decide⟩),
   opAt 1453 .ADD,
   opAt 1454 (.Swap ⟨0, by decide⟩),
   opAt 1455 .SUB,
   opAt 1456 (.Swap ⟨0, by decide⟩),
   pushAt 1457 0 0,
   opAt 1458 .LT,
   opAt 1459 .ADD,
   pushAt 1460 2 9440,
   opAt 1461 .MLOAD,
   pushAt 1462 1 32,
   opAt 1463 (.Swap ⟨0, by decide⟩),
   opAt 1464 .SUB,
   pushAt 1465 2 9408,
   opAt 1466 .MLOAD,
   pushAt 1467 1 32,
   opAt 1468 (.Swap ⟨0, by decide⟩),
   opAt 1469 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
