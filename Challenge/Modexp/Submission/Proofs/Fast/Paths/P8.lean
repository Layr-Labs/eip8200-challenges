import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1421..1468). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1421..1468, pc 1995..2049. -/
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
   pushAt 1424 0 0, opAt 1425 .NOT,
   opAt 1426 (.Swap ⟨1, by decide⟩),
   opAt 1427 .MULMOD,
   opAt 1428 (.Dup ⟨1, by decide⟩),
   opAt 1429 (.Dup ⟨1, by decide⟩),
   opAt 1430 .LT,
   opAt 1431 (.Dup ⟨2, by decide⟩),
   opAt 1432 .ADD,
   opAt 1433 (.Swap ⟨0, by decide⟩),
   opAt 1434 .SUB,
   opAt 1435 (.Dup ⟨3, by decide⟩),
   opAt 1436 .MLOAD,
   opAt 1437 (.Swap ⟨1, by decide⟩),
   opAt 1438 (.Dup ⟨2, by decide⟩),
   opAt 1439 .ADD,
   opAt 1440 (.Swap ⟨1, by decide⟩),
   opAt 1441 (.Dup ⟨2, by decide⟩),
   opAt 1442 .LT,
   opAt 1443 .ADD,
   opAt 1444 (.Swap ⟨0, by decide⟩),
   opAt 1445 (.Dup ⟨4, by decide⟩),
   opAt 1446 .ADD,
   opAt 1447 (.Swap ⟨3, by decide⟩),
   opAt 1448 (.Dup ⟨4, by decide⟩),
   opAt 1449 .LT,
   opAt 1450 .ADD,
   opAt 1451 (.Swap ⟨2, by decide⟩),
   opAt 1452 (.Dup ⟨2, by decide⟩),
   opAt 1453 .MSTORE,
   pushAt 1454 1 31, opAt 1455 .NOT,
   opAt 1456 .ADD,
   opAt 1457 (.Swap ⟨0, by decide⟩),
   pushAt 1458 1 31, opAt 1459 .NOT,
   opAt 1460 .ADD,
   opAt 1461 (.Swap ⟨0, by decide⟩),
   opAt 1462 (.Dup ⟨5, by decide⟩),
   opAt 1463 (.Dup ⟨1, by decide⟩),
   opAt 1464 .GT,
   pushAt 1465 2 1995,
   opAt 1466 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
