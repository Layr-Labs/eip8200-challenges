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
  [opAt 1421 .JUMPDEST,
   pushAt 1422 2 4057,
   opAt 1423 .JUMP,
   pushAt 1424 32 0,
   pushAt 1425 32 0,
   pushAt 1426 1 0,
   pushAt 1427 1 0,
   pushAt 1428 1 0,
   pushAt 1429 1 0,
   pushAt 1430 1 0,
   pushAt 1431 1 0,
   pushAt 1432 1 0,
   pushAt 1433 1 0,
   pushAt 1434 1 0,
   pushAt 1435 1 0,
   pushAt 1436 1 0,
   pushAt 1437 1 0,
   pushAt 1438 1 0,
   pushAt 1439 1 0,
   pushAt 1440 1 0,
   pushAt 1441 1 0,
   pushAt 1442 1 0,
   pushAt 1443 1 0,
   pushAt 1444 1 0,
   pushAt 1445 1 0,
   pushAt 1446 1 0,
   pushAt 1447 1 0,
   pushAt 1448 1 0,
   pushAt 1449 1 0,
   pushAt 1450 1 0,
   pushAt 1451 1 0,
   pushAt 1452 1 0,
   pushAt 1453 1 0,
   pushAt 1454 1 0,
   pushAt 1455 1 0,
   pushAt 1456 1 0,
   pushAt 1457 1 0,
   opAt 1458 .JUMPDEST,
   opAt 1459 .JUMPDEST,
   opAt 1460 .JUMPDEST,
   opAt 1461 .JUMPDEST,
   opAt 1462 .JUMPDEST,
   opAt 1463 .JUMPDEST,
   opAt 1464 .JUMPDEST,
   opAt 1465 .JUMPDEST,
   opAt 1466 .JUMPDEST,
   opAt 1467 .JUMPDEST,
   opAt 1468 .JUMPDEST]

end Challenge.Modexp.Submission.Proofs.Fast
