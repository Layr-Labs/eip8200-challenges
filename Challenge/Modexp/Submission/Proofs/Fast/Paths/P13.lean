import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1683..1741). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1683..1723, pc 2333..2473. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1373 .JUMPDEST,
   opAt 1374 (.Dup ⟨0, by decide⟩),
   opAt 1375 .MLOAD,
   opAt 1376 (.Dup ⟨2, by decide⟩),
   opAt 1377 .MLOAD,
   opAt 1378 (.Dup ⟨1, by decide⟩),
   opAt 1379 (.Dup ⟨1, by decide⟩),
   opAt 1380 .GT,
   opAt 1381 (.Swap ⟨1, by decide⟩),
   opAt 1382 .SUB,
   opAt 1383 (.Dup ⟨5, by decide⟩),
   opAt 1384 (.Dup ⟨1, by decide⟩),
   opAt 1385 .SUB,
   opAt 1386 (.Swap ⟨0, by decide⟩),
   opAt 1387 (.Dup ⟨6, by decide⟩),
   opAt 1388 .GT,
   opAt 1389 (.Swap ⟨0, by decide⟩),
   opAt 1390 (.Swap ⟨1, by decide⟩),
   opAt 1391 .OR,
   opAt 1392 (.Swap ⟨4, by decide⟩),
   opAt 1393 .POP,
   opAt 1394 (.Dup ⟨3, by decide⟩),
   opAt 1395 .MSTORE,
   pushAt 1396 1 31,
   opAt 1397 .NOT,
   opAt 1398 .ADD,
   opAt 1399 (.Swap ⟨0, by decide⟩),
   pushAt 1400 1 31,
   opAt 1401 .NOT,
   opAt 1402 .ADD,
   opAt 1403 (.Swap ⟨0, by decide⟩),
   opAt 1404 (.Swap ⟨1, by decide⟩),
   pushAt 1405 1 31,
   opAt 1406 .NOT,
   opAt 1407 .ADD,
   opAt 1408 (.Swap ⟨1, by decide⟩),
   pushAt 1409 2 8224,
   opAt 1410 (.Dup ⟨1, by decide⟩),
   opAt 1411 .GT,
   pushAt 1412 2 1852,
   opAt 1413 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1414 .POP,
   opAt 1415 .POP,
   opAt 1416 .POP,
   opAt 1417 .ISZERO,
   pushAt 1418 2 8224,
   opAt 1419 .MLOAD,
   opAt 1420 .OR,
   pushAt 1421 2 1087,
   opAt 1422 .NOT,
   opAt 1423 .MUL,
   pushAt 1424 2 8256,
   opAt 1425 .ADD,
   pushAt 1426 2 9344,
   opAt 1427 .MLOAD,
   opAt 1428 (.Swap ⟨1, by decide⟩),
   opAt 1429 .MCOPY,
   opAt 1430 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
