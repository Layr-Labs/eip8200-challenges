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
  [opAt 1408 .JUMPDEST,
   opAt 1409 (.Dup ⟨3, by decide⟩),
   opAt 1410 (.Dup ⟨1, by decide⟩),
   opAt 1411 .MLOAD,
   opAt 1412 (.Dup ⟨1, by decide⟩),
   opAt 1413 (.Dup ⟨1, by decide⟩),
   opAt 1414 .MUL,
   opAt 1415 (.Swap ⟨1, by decide⟩),
   pushAt 1416 0 0, opAt 1417 .NOT,
   opAt 1418 (.Swap ⟨1, by decide⟩),
   opAt 1419 .MULMOD,
   opAt 1420 (.Dup ⟨1, by decide⟩),
   opAt 1421 (.Dup ⟨1, by decide⟩),
   opAt 1422 .LT,
   opAt 1423 (.Dup ⟨2, by decide⟩),
   opAt 1424 .ADD,
   opAt 1425 (.Swap ⟨0, by decide⟩),
   opAt 1426 .SUB,
   opAt 1427 (.Dup ⟨3, by decide⟩),
   opAt 1428 .MLOAD,
   opAt 1429 (.Swap ⟨1, by decide⟩),
   opAt 1430 (.Dup ⟨2, by decide⟩),
   opAt 1431 .ADD,
   opAt 1432 (.Swap ⟨1, by decide⟩),
   opAt 1433 (.Dup ⟨2, by decide⟩),
   opAt 1434 .LT,
   opAt 1435 .ADD,
   opAt 1436 (.Swap ⟨0, by decide⟩),
   opAt 1437 (.Dup ⟨4, by decide⟩),
   opAt 1438 .ADD,
   opAt 1439 (.Swap ⟨3, by decide⟩),
   opAt 1440 (.Dup ⟨4, by decide⟩),
   opAt 1441 .LT,
   opAt 1442 .ADD,
   opAt 1443 (.Swap ⟨2, by decide⟩),
   opAt 1444 (.Dup ⟨2, by decide⟩),
   opAt 1445 .MSTORE,
   pushAt 1446 1 31, opAt 1447 .NOT,
   opAt 1448 .ADD,
   opAt 1449 (.Swap ⟨0, by decide⟩),
   pushAt 1450 1 31, opAt 1451 .NOT,
   opAt 1452 .ADD,
   opAt 1453 (.Swap ⟨0, by decide⟩),
   opAt 1454 (.Dup ⟨5, by decide⟩),
   opAt 1455 (.Dup ⟨1, by decide⟩),
   opAt 1456 .GT,
   pushAt 1457 2 1995,
   opAt 1458 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
