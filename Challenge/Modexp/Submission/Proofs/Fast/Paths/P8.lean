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
  [opAt 1407 .JUMPDEST,
   opAt 1408 (.Dup ⟨3, by decide⟩),
   opAt 1409 (.Dup ⟨1, by decide⟩),
   opAt 1410 .MLOAD,
   opAt 1411 (.Dup ⟨1, by decide⟩),
   opAt 1412 (.Dup ⟨1, by decide⟩),
   opAt 1413 .MUL,
   opAt 1414 (.Swap ⟨1, by decide⟩),
   pushAt 1415 0 0, opAt 1416 .NOT,
   opAt 1417 (.Swap ⟨1, by decide⟩),
   opAt 1418 .MULMOD,
   opAt 1419 (.Dup ⟨1, by decide⟩),
   opAt 1420 (.Dup ⟨1, by decide⟩),
   opAt 1421 .LT,
   opAt 1422 (.Dup ⟨2, by decide⟩),
   opAt 1423 .ADD,
   opAt 1424 (.Swap ⟨0, by decide⟩),
   opAt 1425 .SUB,
   opAt 1426 (.Dup ⟨3, by decide⟩),
   opAt 1427 .MLOAD,
   opAt 1428 (.Swap ⟨1, by decide⟩),
   opAt 1429 (.Dup ⟨2, by decide⟩),
   opAt 1430 .ADD,
   opAt 1431 (.Swap ⟨1, by decide⟩),
   opAt 1432 (.Dup ⟨2, by decide⟩),
   opAt 1433 .LT,
   opAt 1434 .ADD,
   opAt 1435 (.Swap ⟨0, by decide⟩),
   opAt 1436 (.Dup ⟨4, by decide⟩),
   opAt 1437 .ADD,
   opAt 1438 (.Swap ⟨3, by decide⟩),
   opAt 1439 (.Dup ⟨4, by decide⟩),
   opAt 1440 .LT,
   opAt 1441 .ADD,
   opAt 1442 (.Swap ⟨2, by decide⟩),
   opAt 1443 (.Dup ⟨2, by decide⟩),
   opAt 1444 .MSTORE,
   pushAt 1445 1 31, opAt 1446 .NOT,
   opAt 1447 .ADD,
   opAt 1448 (.Swap ⟨0, by decide⟩),
   pushAt 1449 1 31, opAt 1450 .NOT,
   opAt 1451 .ADD,
   opAt 1452 (.Swap ⟨0, by decide⟩),
   opAt 1453 (.Dup ⟨5, by decide⟩),
   opAt 1454 (.Dup ⟨1, by decide⟩),
   opAt 1455 .GT,
   pushAt 1456 2 1986,
   opAt 1457 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
