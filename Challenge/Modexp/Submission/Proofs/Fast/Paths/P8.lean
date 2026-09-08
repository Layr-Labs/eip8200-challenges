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
  [opAt 1408 .JUMPDEST,
   pushAt 1409 2 3905,
   opAt 1410 .JUMP,
   pushAt 1411 0 0,
   pushAt 1412 0 0,
   pushAt 1413 0 0,
   pushAt 1414 0 0,
   pushAt 1415 0 0,
   pushAt 1416 0 0,
   pushAt 1417 0 0,
   pushAt 1418 0 0,
   pushAt 1419 0 0,
   pushAt 1420 0 0,
   pushAt 1421 0 0,
   pushAt 1422 0 0,
   pushAt 1423 0 0,
   pushAt 1424 0 0,
   pushAt 1425 0 0,
   pushAt 1426 0 0,
   pushAt 1427 0 0,
   pushAt 1428 0 0,
   pushAt 1429 0 0,
   pushAt 1430 0 0,
   pushAt 1431 0 0,
   pushAt 1432 0 0,
   pushAt 1433 0 0,
   pushAt 1434 0 0,
   pushAt 1435 0 0,
   pushAt 1436 0 0,
   pushAt 1437 0 0,
   pushAt 1438 0 0,
   pushAt 1439 0 0,
   pushAt 1440 0 0,
   pushAt 1441 0 0,
   pushAt 1442 0 0,
   pushAt 1443 0 0,
   pushAt 1444 0 0,
                                 opAt 1445 .JUMPDEST]

end Challenge.Modexp.Submission.Proofs.Fast
