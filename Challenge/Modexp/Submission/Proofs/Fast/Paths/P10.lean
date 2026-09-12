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
  [opAt 1403 .JUMPDEST,
   opAt 1404 (.Dup ⟨0, by decide⟩),
   opAt 1405 .MLOAD,
   pushAt 1406 0 0,
   opAt 1407 .NOT,
   opAt 1408 (.Dup ⟨5, by decide⟩),
   opAt 1409 (.Dup ⟨2, by decide⟩),
   opAt 1410 .MUL,
   opAt 1411 (.Swap ⟨1, by decide⟩),
   opAt 1412 (.Dup ⟨6, by decide⟩),
   opAt 1413 .MULMOD,
   opAt 1414 (.Dup ⟨1, by decide⟩),
   opAt 1415 (.Dup ⟨1, by decide⟩),
   opAt 1416 .LT,
   opAt 1417 .SUB,
   opAt 1418 (.Dup ⟨4, by decide⟩),
   opAt 1419 (.Dup ⟨2, by decide⟩),
   opAt 1420 .ADD,
   opAt 1421 (.Dup ⟨0, by decide⟩),
   opAt 1422 (.Swap ⟨5, by decide⟩),
   opAt 1423 .GT,
   opAt 1424 .SUB,
   opAt 1425 .SUB,
   opAt 1426 (.Dup ⟨3, by decide⟩),
   opAt 1427 (.Dup ⟨3, by decide⟩),
   opAt 1428 .MLOAD,
   opAt 1429 .ADD,
   opAt 1430 (.Dup ⟨0, by decide⟩),
   opAt 1431 (.Swap ⟨4, by decide⟩),
   opAt 1432 .GT,
   opAt 1433 .ADD,
   opAt 1434 (.Swap ⟨2, by decide⟩),
   pushAt 1435 1 32,
   opAt 1436 (.Dup ⟨3, by decide⟩),
   pushAt 1437 1 31,
   opAt 1438 .NOT,
   opAt 1439 .ADD,
   opAt 1440 (.Swap ⟨3, by decide⟩),
   opAt 1441 .ADD,
   opAt 1442 .MSTORE,
   pushAt 1443 1 31,
   opAt 1444 .NOT,
   opAt 1445 .ADD,
   pushAt 1446 2 8224,
   opAt 1447 (.Dup ⟨2, by decide⟩),
   opAt 1448 .GT,
   pushAt 1449 2 1934,
   opAt 1450 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
