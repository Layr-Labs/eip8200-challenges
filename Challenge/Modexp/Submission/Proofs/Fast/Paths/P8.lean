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
  [opAt 1416 .JUMPDEST,
   opAt 1417 (.Dup ⟨3, by decide⟩),
   opAt 1418 (.Dup ⟨1, by decide⟩),
   opAt 1419 .MLOAD,
   opAt 1420 (.Dup ⟨1, by decide⟩),
   opAt 1421 (.Dup ⟨1, by decide⟩),
   opAt 1422 .MUL,
   opAt 1423 (.Swap ⟨1, by decide⟩),
   pushAt 1424 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1425 (.Swap ⟨1, by decide⟩),
   opAt 1426 .MULMOD,
   opAt 1427 (.Dup ⟨1, by decide⟩),
   opAt 1428 (.Dup ⟨1, by decide⟩),
   opAt 1429 .LT,
   opAt 1430 (.Dup ⟨2, by decide⟩),
   opAt 1431 .ADD,
   opAt 1432 (.Swap ⟨0, by decide⟩),
   opAt 1433 .SUB,
   opAt 1434 (.Dup ⟨3, by decide⟩),
   opAt 1435 .MLOAD,
   opAt 1436 (.Swap ⟨1, by decide⟩),
   opAt 1437 (.Dup ⟨2, by decide⟩),
   opAt 1438 .ADD,
   opAt 1439 (.Swap ⟨1, by decide⟩),
   opAt 1440 (.Dup ⟨2, by decide⟩),
   opAt 1441 .LT,
   opAt 1442 .ADD,
   opAt 1443 (.Swap ⟨0, by decide⟩),
   opAt 1444 (.Dup ⟨4, by decide⟩),
   opAt 1445 .ADD,
   opAt 1446 (.Swap ⟨3, by decide⟩),
   opAt 1447 (.Dup ⟨4, by decide⟩),
   opAt 1448 .LT,
   opAt 1449 .ADD,
   opAt 1450 (.Swap ⟨2, by decide⟩),
   opAt 1451 (.Dup ⟨2, by decide⟩),
   opAt 1452 .MSTORE,
   pushAt 1453 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1454 .ADD,
   opAt 1455 (.Swap ⟨0, by decide⟩),
   pushAt 1456 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1457 .ADD,
   opAt 1458 (.Swap ⟨0, by decide⟩),
   opAt 1459 (.Dup ⟨5, by decide⟩),
   opAt 1460 (.Dup ⟨1, by decide⟩),
   opAt 1461 .GT,
   pushAt 1462 2 1988,
   opAt 1463 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
