import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1421..1468). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1421..1468, pc 1995..2140. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1422 .JUMPDEST,
   opAt 1423 (.Dup ⟨3, by decide⟩),
   opAt 1424 (.Dup ⟨1, by decide⟩),
   opAt 1425 .MLOAD,
   opAt 1426 (.Dup ⟨1, by decide⟩),
   opAt 1427 (.Dup ⟨1, by decide⟩),
   opAt 1428 .MUL,
   opAt 1429 (.Swap ⟨1, by decide⟩),
   pushAt 1430 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1431 (.Swap ⟨1, by decide⟩),
   opAt 1432 .MULMOD,
   opAt 1433 (.Dup ⟨1, by decide⟩),
   opAt 1434 (.Dup ⟨1, by decide⟩),
   opAt 1435 .LT,
   opAt 1436 (.Dup ⟨2, by decide⟩),
   opAt 1437 .ADD,
   opAt 1438 (.Swap ⟨0, by decide⟩),
   opAt 1439 .SUB,
   opAt 1440 (.Dup ⟨3, by decide⟩),
   opAt 1441 .MLOAD,
   opAt 1442 (.Swap ⟨1, by decide⟩),
   opAt 1443 (.Dup ⟨2, by decide⟩),
   opAt 1444 .ADD,
   opAt 1445 (.Swap ⟨1, by decide⟩),
   opAt 1446 (.Dup ⟨2, by decide⟩),
   opAt 1447 .LT,
   opAt 1448 .ADD,
   opAt 1449 (.Swap ⟨0, by decide⟩),
   opAt 1450 (.Dup ⟨4, by decide⟩),
   opAt 1451 .ADD,
   opAt 1452 (.Swap ⟨3, by decide⟩),
   opAt 1453 (.Dup ⟨4, by decide⟩),
   opAt 1454 .LT,
   opAt 1455 .ADD,
   opAt 1456 (.Swap ⟨2, by decide⟩),
   opAt 1457 (.Dup ⟨2, by decide⟩),
   opAt 1458 .MSTORE,
   pushAt 1459 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1460 .ADD,
   opAt 1461 (.Swap ⟨0, by decide⟩),
   pushAt 1462 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1463 .ADD,
   opAt 1464 (.Swap ⟨0, by decide⟩),
   opAt 1465 (.Dup ⟨5, by decide⟩),
   opAt 1466 (.Dup ⟨1, by decide⟩),
   opAt 1467 .GT,
   pushAt 1468 2 1995,
   opAt 1469 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
