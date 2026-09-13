import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1644..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1644..1568, pc 2196..2303. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1398 .JUMPDEST,
   opAt 1399 (.Dup ⟨0, by decide⟩),
   opAt 1400 .MLOAD,
   pushAt 1401 0 0,
   opAt 1402 .NOT,
   opAt 1403 (.Dup ⟨5, by decide⟩),
   opAt 1404 (.Dup ⟨2, by decide⟩),
   opAt 1405 .MUL,
   opAt 1406 (.Swap ⟨1, by decide⟩),
   opAt 1407 (.Dup ⟨6, by decide⟩),
   opAt 1408 .MULMOD,
   opAt 1409 (.Dup ⟨1, by decide⟩),
   opAt 1410 (.Dup ⟨1, by decide⟩),
   opAt 1411 .LT,
   opAt 1412 .SUB,
   opAt 1413 (.Dup ⟨4, by decide⟩),
   opAt 1414 (.Dup ⟨2, by decide⟩),
   opAt 1415 .ADD,
   opAt 1416 (.Dup ⟨0, by decide⟩),
   opAt 1417 (.Swap ⟨5, by decide⟩),
   opAt 1418 .GT,
   opAt 1419 .SUB,
   opAt 1420 .SUB,
   opAt 1421 (.Dup ⟨3, by decide⟩),
   opAt 1422 (.Dup ⟨3, by decide⟩),
   opAt 1423 .MLOAD,
   opAt 1424 .ADD,
   opAt 1425 (.Dup ⟨0, by decide⟩),
   opAt 1426 (.Swap ⟨4, by decide⟩),
   opAt 1427 .GT,
   opAt 1428 .ADD,
   opAt 1429 (.Swap ⟨2, by decide⟩),
   pushAt 1430 1 32,
   opAt 1431 (.Dup ⟨3, by decide⟩),
   pushAt 1432 1 31,
   opAt 1433 .NOT,
   opAt 1434 .ADD,
   opAt 1435 (.Swap ⟨3, by decide⟩),
   opAt 1436 .ADD,
   opAt 1437 .MSTORE,
   pushAt 1438 1 31,
   opAt 1439 .NOT,
   opAt 1440 .ADD,
   pushAt 1441 2 2080,
   opAt 1442 (.Dup ⟨2, by decide⟩),
   opAt 1443 .GT,
   pushAt 1444 2 1924,
   opAt 1445 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
