import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1626). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1594, pc 2179..2459. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1376 .POP,
   opAt 1377 .POP,
   opAt 1378 (.Swap ⟨1, by decide⟩),
   opAt 1379 .POP,
   opAt 1380 .POP,
   opAt 1381 (.Dup ⟨0, by decide⟩),
   pushAt 1382 2 2080,
   opAt 1383 .MLOAD,
   opAt 1384 .ADD,
   opAt 1385 (.Dup ⟨0, by decide⟩),
   pushAt 1386 2 2112,
   opAt 1387 .MSTORE,
   opAt 1388 .LT,
   pushAt 1389 2 2048,
   opAt 1390 .MLOAD,
   opAt 1391 .ADD,
   pushAt 1392 2 2080,
   opAt 1393 .MSTORE,
   pushAt 1394 1 31,
   opAt 1395 .NOT,
   opAt 1396 .ADD,
   opAt 1397 (.Dup ⟨2, by decide⟩),
   opAt 1398 (.Dup ⟨1, by decide⟩),
   opAt 1399 .GT,
   pushAt 1400 2 1661,
   opAt 1401 .JUMPI]

/-- Instructions 1595..1599, pc 2460..2223. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1402 .POP,
   opAt 1403 .POP,
   opAt 1404 .POP,
   pushAt 1405 2 4669,
   opAt 1406 .JUMP]

/-- Instructions 1600..1626, pc 2224..2256. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1407 .JUMPDEST,
   pushAt 1408 2 2784,
   opAt 1409 .MLOAD,
   opAt 1410 (.Dup ⟨0, by decide⟩),
   opAt 1411 (.Dup ⟨2, by decide⟩),
   opAt 1412 .ADD,
   pushAt 1413 1 32,
   opAt 1414 (.Swap ⟨0, by decide⟩),
   opAt 1415 .SUB,
   opAt 1416 (.Dup ⟨1, by decide⟩),
   opAt 1417 (.Dup ⟨4, by decide⟩),
   opAt 1418 .ADD,
   pushAt 1419 1 32,
   opAt 1420 (.Swap ⟨0, by decide⟩),
   opAt 1421 .SUB,
   opAt 1422 (.Swap ⟨2, by decide⟩),
   opAt 1423 .POP,
   opAt 1424 (.Swap ⟨2, by decide⟩),
   opAt 1425 .POP,
   opAt 1426 .POP,
   pushAt 1427 2 2880,
   opAt 1428 .MLOAD,
   pushAt 1429 0 0,
   opAt 1430 (.Swap ⟨2, by decide⟩),
   opAt 1431 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
