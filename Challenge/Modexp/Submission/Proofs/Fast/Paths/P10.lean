import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1644..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1644..1568, pc 2198..2305. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1400 .JUMPDEST,
   opAt 1401 (.Dup ⟨0, by decide⟩),
   opAt 1402 .MLOAD,
   pushAt 1403 0 0,
   opAt 1404 .NOT,
   opAt 1405 (.Dup ⟨5, by decide⟩),
   opAt 1406 (.Dup ⟨2, by decide⟩),
   opAt 1407 .MUL,
   opAt 1408 (.Swap ⟨1, by decide⟩),
   opAt 1409 (.Dup ⟨6, by decide⟩),
   opAt 1410 .MULMOD,
   opAt 1411 (.Dup ⟨1, by decide⟩),
   opAt 1412 (.Dup ⟨1, by decide⟩),
   opAt 1413 .LT,
   opAt 1414 .SUB,
   opAt 1415 (.Dup ⟨4, by decide⟩),
   opAt 1416 (.Dup ⟨2, by decide⟩),
   opAt 1417 .ADD,
   opAt 1418 (.Dup ⟨0, by decide⟩),
   opAt 1419 (.Swap ⟨5, by decide⟩),
   opAt 1420 .GT,
   opAt 1421 .SUB,
   opAt 1422 .SUB,
   opAt 1423 (.Dup ⟨3, by decide⟩),
   opAt 1424 (.Dup ⟨3, by decide⟩),
   opAt 1425 .MLOAD,
   opAt 1426 .ADD,
   opAt 1427 (.Dup ⟨0, by decide⟩),
   opAt 1428 (.Swap ⟨4, by decide⟩),
   opAt 1429 .GT,
   opAt 1430 .ADD,
   opAt 1431 (.Swap ⟨2, by decide⟩),
   pushAt 1432 1 32,
   opAt 1433 (.Dup ⟨3, by decide⟩),
   pushAt 1434 1 31,
   opAt 1435 .NOT,
   opAt 1436 .ADD,
   opAt 1437 (.Swap ⟨3, by decide⟩),
   opAt 1438 .ADD,
   opAt 1439 .MSTORE,
   pushAt 1440 1 31,
   opAt 1441 .NOT,
   opAt 1442 .ADD,
   pushAt 1443 2 2080,
   opAt 1444 (.Dup ⟨2, by decide⟩),
   opAt 1445 .GT,
   pushAt 1446 2 1926,
   opAt 1447 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
