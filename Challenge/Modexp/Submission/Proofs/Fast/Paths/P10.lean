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
  [opAt 1395 .JUMPDEST,
   opAt 1396 (.Dup ⟨0, by decide⟩),
   opAt 1397 .MLOAD,
   pushAt 1398 0 0,
   opAt 1399 .NOT,
   opAt 1400 (.Dup ⟨5, by decide⟩),
   opAt 1401 (.Dup ⟨2, by decide⟩),
   opAt 1402 .MUL,
   opAt 1403 (.Swap ⟨1, by decide⟩),
   opAt 1404 (.Dup ⟨6, by decide⟩),
   opAt 1405 .MULMOD,
   opAt 1406 (.Dup ⟨1, by decide⟩),
   opAt 1407 (.Dup ⟨1, by decide⟩),
   opAt 1408 .LT,
   opAt 1409 .SUB,
   opAt 1410 (.Dup ⟨4, by decide⟩),
   opAt 1411 (.Dup ⟨2, by decide⟩),
   opAt 1412 .ADD,
   opAt 1413 (.Dup ⟨0, by decide⟩),
   opAt 1414 (.Swap ⟨5, by decide⟩),
   opAt 1415 .GT,
   opAt 1416 .SUB,
   opAt 1417 .SUB,
   opAt 1418 (.Dup ⟨3, by decide⟩),
   opAt 1419 (.Dup ⟨3, by decide⟩),
   opAt 1420 .MLOAD,
   opAt 1421 .ADD,
   opAt 1422 (.Dup ⟨0, by decide⟩),
   opAt 1423 (.Swap ⟨4, by decide⟩),
   opAt 1424 .GT,
   opAt 1425 .ADD,
   opAt 1426 (.Swap ⟨2, by decide⟩),
   pushAt 1427 1 32,
   opAt 1428 (.Dup ⟨3, by decide⟩),
   pushAt 1429 1 31,
   opAt 1430 .NOT,
   opAt 1431 .ADD,
   opAt 1432 (.Swap ⟨3, by decide⟩),
   opAt 1433 .ADD,
   opAt 1434 .MSTORE,
   pushAt 1435 1 31,
   opAt 1436 .NOT,
   opAt 1437 .ADD,
   pushAt 1438 2 2080,
   opAt 1439 (.Dup ⟨2, by decide⟩),
   opAt 1440 .GT,
   pushAt 1441 2 1926,
   opAt 1442 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
