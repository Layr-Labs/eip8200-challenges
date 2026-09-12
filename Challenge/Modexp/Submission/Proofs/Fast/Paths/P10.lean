import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1519..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1519..1568, pc 2119..2178. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1404 .JUMPDEST,
   opAt 1405 (.Dup ⟨0, by decide⟩),
   opAt 1406 .MLOAD,
   pushAt 1407 0 0,
   opAt 1408 .NOT,
   opAt 1409 (.Dup ⟨5, by decide⟩),
   opAt 1410 (.Dup ⟨2, by decide⟩),
   opAt 1411 .MUL,
   opAt 1412 (.Swap ⟨1, by decide⟩),
   opAt 1413 (.Dup ⟨6, by decide⟩),
   opAt 1414 .MULMOD,
   opAt 1415 (.Dup ⟨1, by decide⟩),
   opAt 1416 (.Dup ⟨1, by decide⟩),
   opAt 1417 .LT,
   opAt 1418 .SUB,
   opAt 1419 (.Dup ⟨4, by decide⟩),
   opAt 1420 (.Dup ⟨2, by decide⟩),
   opAt 1421 .ADD,
   opAt 1422 (.Dup ⟨0, by decide⟩),
   opAt 1423 (.Swap ⟨5, by decide⟩),
   opAt 1424 .GT,
   opAt 1425 .SUB,
   opAt 1426 .SUB,
   opAt 1427 (.Dup ⟨3, by decide⟩),
   opAt 1428 (.Dup ⟨3, by decide⟩),
   opAt 1429 .MLOAD,
   opAt 1430 .ADD,
   opAt 1431 (.Dup ⟨0, by decide⟩),
   opAt 1432 (.Swap ⟨4, by decide⟩),
   opAt 1433 .GT,
   opAt 1434 .ADD,
   opAt 1435 (.Swap ⟨2, by decide⟩),
   pushAt 1436 1 32,
   opAt 1437 (.Dup ⟨3, by decide⟩),
   pushAt 1438 1 31,
   opAt 1439 .NOT,
   opAt 1440 .ADD,
   opAt 1441 (.Swap ⟨3, by decide⟩),
   opAt 1442 .ADD,
   opAt 1443 .MSTORE,
   pushAt 1444 1 31,
   opAt 1445 .NOT,
   opAt 1446 .ADD,
   pushAt 1447 2 4128,
   opAt 1448 (.Dup ⟨2, by decide⟩),
   opAt 1449 .GT,
   pushAt 1450 2 1934,
   opAt 1451 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
