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
  [opAt 1412 .JUMPDEST,
   opAt 1413 (.Dup ⟨3, by decide⟩),
   opAt 1414 (.Dup ⟨1, by decide⟩),
   opAt 1415 .MLOAD,
   opAt 1416 (.Dup ⟨1, by decide⟩),
   opAt 1417 (.Dup ⟨1, by decide⟩),
   opAt 1418 .MUL,
   opAt 1419 (.Swap ⟨1, by decide⟩),
   pushAt 1420 0 0, opAt 1421 .NOT,
   opAt 1422 (.Swap ⟨1, by decide⟩),
   opAt 1423 .MULMOD,
   opAt 1424 (.Dup ⟨1, by decide⟩),
   opAt 1425 (.Dup ⟨1, by decide⟩),
   opAt 1426 .LT,
   opAt 1427 (.Dup ⟨2, by decide⟩),
   opAt 1428 .ADD,
   opAt 1429 (.Swap ⟨0, by decide⟩),
   opAt 1430 .SUB,
   opAt 1431 (.Dup ⟨3, by decide⟩),
   opAt 1432 .MLOAD,
   opAt 1433 (.Swap ⟨1, by decide⟩),
   opAt 1434 (.Dup ⟨2, by decide⟩),
   opAt 1435 .ADD,
   opAt 1436 (.Swap ⟨1, by decide⟩),
   opAt 1437 (.Dup ⟨2, by decide⟩),
   opAt 1438 .LT,
   opAt 1439 .ADD,
   opAt 1440 (.Swap ⟨0, by decide⟩),
   opAt 1441 (.Dup ⟨4, by decide⟩),
   opAt 1442 .ADD,
   opAt 1443 (.Swap ⟨3, by decide⟩),
   opAt 1444 (.Dup ⟨4, by decide⟩),
   opAt 1445 .LT,
   opAt 1446 .ADD,
   opAt 1447 (.Swap ⟨2, by decide⟩),
   opAt 1448 (.Dup ⟨2, by decide⟩),
   opAt 1449 .MSTORE,
   pushAt 1450 1 31, opAt 1451 .NOT,
   opAt 1452 .ADD,
   opAt 1453 (.Swap ⟨0, by decide⟩),
   pushAt 1454 1 31, opAt 1455 .NOT,
   opAt 1456 .ADD,
   opAt 1457 (.Swap ⟨0, by decide⟩),
   opAt 1458 (.Dup ⟨5, by decide⟩),
   opAt 1459 (.Dup ⟨1, by decide⟩),
   opAt 1460 .GT,
   pushAt 1461 2 1995,
   opAt 1462 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
