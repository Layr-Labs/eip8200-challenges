import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1626). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1594, pc 2179..2459. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1400 .POP,
   opAt 1401 .POP,
   opAt 1402 (.Swap ⟨1, by decide⟩),
   opAt 1403 .POP,
   opAt 1404 .POP,
   opAt 1405 (.Dup ⟨0, by decide⟩),
   pushAt 1406 2 8224,
   opAt 1407 .MLOAD,
   opAt 1408 .ADD,
   opAt 1409 (.Dup ⟨0, by decide⟩),
   pushAt 1410 2 8256,
   opAt 1411 .MSTORE,
   opAt 1412 .LT,
   pushAt 1413 2 8192,
   opAt 1414 .MLOAD,
   opAt 1415 .ADD,
   pushAt 1416 2 8224,
   opAt 1417 .MSTORE,
   pushAt 1418 1 31,
   opAt 1419 .NOT,
   opAt 1420 .ADD,
   opAt 1421 (.Dup ⟨2, by decide⟩),
   opAt 1422 (.Dup ⟨1, by decide⟩),
   opAt 1423 .GT,
   pushAt 1424 2 1702,
   opAt 1425 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1426 .POP,
   opAt 1427 .POP,
   opAt 1428 .POP,
   pushAt 1429 2 4667,
   opAt 1430 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1431 .JUMPDEST,
   pushAt 1432 2 9344,
   opAt 1433 .MLOAD,
   opAt 1434 (.Dup ⟨0, by decide⟩),
   opAt 1435 (.Dup ⟨2, by decide⟩),
   opAt 1436 .ADD,
   pushAt 1437 1 32,
   opAt 1438 (.Swap ⟨0, by decide⟩),
   opAt 1439 .SUB,
   opAt 1440 (.Dup ⟨1, by decide⟩),
   opAt 1441 (.Dup ⟨4, by decide⟩),
   opAt 1442 .ADD,
   pushAt 1443 1 32,
   opAt 1444 (.Swap ⟨0, by decide⟩),
   opAt 1445 .SUB,
   opAt 1446 (.Swap ⟨2, by decide⟩),
   opAt 1447 .POP,
   opAt 1448 (.Swap ⟨2, by decide⟩),
   opAt 1449 .POP,
   opAt 1450 .POP,
   pushAt 1451 2 9440,
   opAt 1452 .MLOAD,
   pushAt 1453 0 0,
   opAt 1454 (.Swap ⟨2, by decide⟩),
   opAt 1455 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
