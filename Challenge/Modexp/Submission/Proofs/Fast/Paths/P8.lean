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
  [opAt 1410 .JUMPDEST,
   opAt 1411 (.Dup ⟨3, by decide⟩),
   opAt 1412 (.Dup ⟨1, by decide⟩),
   opAt 1413 .MLOAD,
   opAt 1414 (.Dup ⟨1, by decide⟩),
   opAt 1415 (.Dup ⟨1, by decide⟩),
   opAt 1416 .MUL,
   opAt 1417 (.Swap ⟨1, by decide⟩),
   pushAt 1418 0 0, opAt 1419 .NOT,
   opAt 1420 (.Swap ⟨1, by decide⟩),
   opAt 1421 .MULMOD,
   opAt 1422 (.Dup ⟨1, by decide⟩),
   opAt 1423 (.Dup ⟨1, by decide⟩),
   opAt 1424 .LT,
   opAt 1425 (.Dup ⟨2, by decide⟩),
   opAt 1426 .ADD,
   opAt 1427 (.Swap ⟨0, by decide⟩),
   opAt 1428 .SUB,
   opAt 1429 (.Dup ⟨3, by decide⟩),
   opAt 1430 .MLOAD,
   opAt 1431 (.Swap ⟨1, by decide⟩),
   opAt 1432 (.Dup ⟨2, by decide⟩),
   opAt 1433 .ADD,
   opAt 1434 (.Swap ⟨1, by decide⟩),
   opAt 1435 (.Dup ⟨2, by decide⟩),
   opAt 1436 .LT,
   opAt 1437 .ADD,
   opAt 1438 (.Swap ⟨0, by decide⟩),
   opAt 1439 (.Dup ⟨4, by decide⟩),
   opAt 1440 .ADD,
   opAt 1441 (.Swap ⟨3, by decide⟩),
   opAt 1442 (.Dup ⟨4, by decide⟩),
   opAt 1443 .LT,
   opAt 1444 .ADD,
   opAt 1445 (.Swap ⟨2, by decide⟩),
   opAt 1446 (.Dup ⟨2, by decide⟩),
   opAt 1447 .MSTORE,
   pushAt 1448 1 31, opAt 1449 .NOT,
   opAt 1450 .ADD,
   opAt 1451 (.Swap ⟨0, by decide⟩),
   pushAt 1452 1 31, opAt 1453 .NOT,
   opAt 1454 .ADD,
   opAt 1455 (.Swap ⟨0, by decide⟩),
   opAt 1456 (.Dup ⟨5, by decide⟩),
   opAt 1457 (.Dup ⟨1, by decide⟩),
   opAt 1458 .GT,
   pushAt 1459 2 1979,
   opAt 1460 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
