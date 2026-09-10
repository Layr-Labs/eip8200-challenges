import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1421..1468). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1421..1468, pc 1995..2049. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1398 .JUMPDEST,
   opAt 1399 (.Dup ⟨3, by decide⟩),
   opAt 1400 (.Dup ⟨1, by decide⟩),
   opAt 1401 .MLOAD,
   opAt 1402 (.Dup ⟨1, by decide⟩),
   opAt 1403 (.Dup ⟨1, by decide⟩),
   opAt 1404 .MUL,
   opAt 1405 (.Swap ⟨1, by decide⟩),
   pushAt 1406 0 0,
   opAt 1407 .NOT,
   opAt 1408 (.Swap ⟨1, by decide⟩),
   opAt 1409 .MULMOD,
   opAt 1410 (.Dup ⟨1, by decide⟩),
   opAt 1411 (.Dup ⟨1, by decide⟩),
   opAt 1412 .LT,
   opAt 1413 (.Dup ⟨2, by decide⟩),
   opAt 1414 .ADD,
   opAt 1415 (.Swap ⟨0, by decide⟩),
   opAt 1416 .SUB,
   opAt 1417 (.Dup ⟨3, by decide⟩),
   opAt 1418 .MLOAD,
   opAt 1419 (.Swap ⟨1, by decide⟩),
   opAt 1420 (.Dup ⟨2, by decide⟩),
   opAt 1421 .ADD,
   opAt 1422 (.Swap ⟨1, by decide⟩),
   opAt 1423 (.Dup ⟨2, by decide⟩),
   opAt 1424 .LT,
   opAt 1425 .ADD,
   opAt 1426 (.Swap ⟨0, by decide⟩),
   opAt 1427 (.Dup ⟨4, by decide⟩),
   opAt 1428 .ADD,
   opAt 1429 (.Swap ⟨3, by decide⟩),
   opAt 1430 (.Dup ⟨4, by decide⟩),
   opAt 1431 .LT,
   opAt 1432 .ADD,
   opAt 1433 (.Swap ⟨2, by decide⟩),
   opAt 1434 (.Dup ⟨2, by decide⟩),
   opAt 1435 .MSTORE,
   pushAt 1436 1 31,
   opAt 1437 .NOT,
   opAt 1438 .ADD,
   opAt 1439 (.Swap ⟨0, by decide⟩),
   pushAt 1440 1 31,
   opAt 1441 .NOT,
   opAt 1442 .ADD,
   opAt 1443 (.Swap ⟨0, by decide⟩),
   opAt 1444 (.Dup ⟨5, by decide⟩),
   opAt 1445 (.Dup ⟨1, by decide⟩),
   opAt 1446 .GT,
   pushAt 1447 2 1976,
   opAt 1448 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
