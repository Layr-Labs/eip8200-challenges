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
  [opAt 1396 .JUMPDEST,
   opAt 1397 (.Dup ⟨0, by decide⟩),
   opAt 1398 .MLOAD,
   pushAt 1399 0 0,
   opAt 1400 .NOT,
   opAt 1401 (.Dup ⟨5, by decide⟩),
   opAt 1402 (.Dup ⟨2, by decide⟩),
   opAt 1403 .MUL,
   opAt 1404 (.Swap ⟨1, by decide⟩),
   opAt 1405 (.Dup ⟨6, by decide⟩),
   opAt 1406 .MULMOD,
   opAt 1407 (.Dup ⟨1, by decide⟩),
   opAt 1408 (.Dup ⟨1, by decide⟩),
   opAt 1409 .LT,
   opAt 1410 .SUB,
   opAt 1411 (.Dup ⟨4, by decide⟩),
   opAt 1412 (.Dup ⟨2, by decide⟩),
   opAt 1413 .ADD,
   opAt 1414 (.Dup ⟨0, by decide⟩),
   opAt 1415 (.Swap ⟨5, by decide⟩),
   opAt 1416 .GT,
   opAt 1417 .SUB,
   opAt 1418 .SUB,
   opAt 1419 (.Dup ⟨3, by decide⟩),
   opAt 1420 (.Dup ⟨3, by decide⟩),
   opAt 1421 .MLOAD,
   opAt 1422 .ADD,
   opAt 1423 (.Dup ⟨0, by decide⟩),
   opAt 1424 (.Swap ⟨4, by decide⟩),
   opAt 1425 .GT,
   opAt 1426 .ADD,
   opAt 1427 (.Swap ⟨2, by decide⟩),
   pushAt 1428 1 32,
   opAt 1429 (.Dup ⟨3, by decide⟩),
   pushAt 1430 1 31,
   opAt 1431 .NOT,
   opAt 1432 .ADD,
   opAt 1433 (.Swap ⟨3, by decide⟩),
   opAt 1434 .ADD,
   opAt 1435 .MSTORE,
   pushAt 1436 1 31,
   opAt 1437 .NOT,
   opAt 1438 .ADD,
   pushAt 1439 2 2080,
   opAt 1440 (.Dup ⟨2, by decide⟩),
   opAt 1441 .GT,
   pushAt 1442 2 1926,
   opAt 1443 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
