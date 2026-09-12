import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1649..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1649..1568, pc 2201..2308. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1401 .JUMPDEST,
   opAt 1402 (.Dup ⟨0, by decide⟩),
   opAt 1403 .MLOAD,
   pushAt 1404 0 0,
   opAt 1405 .NOT,
   opAt 1406 (.Dup ⟨5, by decide⟩),
   opAt 1407 (.Dup ⟨2, by decide⟩),
   opAt 1408 .MUL,
   opAt 1409 (.Swap ⟨1, by decide⟩),
   opAt 1410 (.Dup ⟨6, by decide⟩),
   opAt 1411 .MULMOD,
   opAt 1412 (.Dup ⟨1, by decide⟩),
   opAt 1413 (.Dup ⟨1, by decide⟩),
   opAt 1414 .LT,
   opAt 1415 .SUB,
   opAt 1416 (.Dup ⟨4, by decide⟩),
   opAt 1417 (.Dup ⟨2, by decide⟩),
   opAt 1418 .ADD,
   opAt 1419 (.Dup ⟨0, by decide⟩),
   opAt 1420 (.Swap ⟨5, by decide⟩),
   opAt 1421 .GT,
   opAt 1422 .SUB,
   opAt 1423 .SUB,
   opAt 1424 (.Dup ⟨3, by decide⟩),
   opAt 1425 (.Dup ⟨3, by decide⟩),
   opAt 1426 .MLOAD,
   opAt 1427 .ADD,
   opAt 1428 (.Dup ⟨0, by decide⟩),
   opAt 1429 (.Swap ⟨4, by decide⟩),
   opAt 1430 .GT,
   opAt 1431 .ADD,
   opAt 1432 (.Swap ⟨2, by decide⟩),
   pushAt 1433 1 32,
   opAt 1434 (.Dup ⟨3, by decide⟩),
   pushAt 1435 1 31,
   opAt 1436 .NOT,
   opAt 1437 .ADD,
   opAt 1438 (.Swap ⟨3, by decide⟩),
   opAt 1439 .ADD,
   opAt 1440 .MSTORE,
   pushAt 1441 1 31,
   opAt 1442 .NOT,
   opAt 1443 .ADD,
   pushAt 1444 2 4128,
   opAt 1445 (.Dup ⟨2, by decide⟩),
   opAt 1446 .GT,
   pushAt 1447 2 1929,
   opAt 1448 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
