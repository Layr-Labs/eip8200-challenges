import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1369..1420). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1369..1375, pc 1926..1935. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1369 .JUMPDEST,
   pushAt 1370 0 0,
   opAt 1371 .NOT,
   opAt 1372 .ADD,
   opAt 1373 (.Dup ⟨0, by decide⟩),
   pushAt 1374 2 1915,
   opAt 1375 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1376 .POP,
   opAt 1377 .POP,
   opAt 1378 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1380 .JUMPDEST,
   pushAt 1381 2 9344,
   opAt 1382 .MLOAD,
   opAt 1383 (.Dup ⟨0, by decide⟩),
   pushAt 1384 1 64,
   opAt 1385 .ADD,
   opAt 1386 .CALLDATASIZE,
   pushAt 1387 2 8192,
   opAt 1388 .CALLDATACOPY,
   opAt 1389 (.Dup ⟨0, by decide⟩),
   opAt 1390 (.Dup ⟨3, by decide⟩),
   opAt 1391 .ADD,
   pushAt 1392 1 32,
   opAt 1393 (.Swap ⟨0, by decide⟩),
   opAt 1394 .SUB,
   pushAt 1395 1 32,
   opAt 1396 (.Dup ⟨4, by decide⟩),
   opAt 1397 .SUB,
   opAt 1398 (.Swap ⟨3, by decide⟩),
   opAt 1399 .POP,
   opAt 1400 (.Swap ⟨0, by decide⟩),
   opAt 1401 .POP,
   pushAt 1402 1 32,
   opAt 1403 (.Dup ⟨2, by decide⟩),
   opAt 1404 .SUB,
   opAt 1405 (.Swap ⟨1, by decide⟩),
   opAt 1406 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1407 .JUMPDEST,
   opAt 1408 (.Dup ⟨0, by decide⟩),
   opAt 1409 .MLOAD,
   pushAt 1410 0 0,
   pushAt 1411 2 9440,
   opAt 1412 .MLOAD,
   opAt 1413 (.Dup ⟨4, by decide⟩),
   pushAt 1414 1 32,
   opAt 1415 .ADD,
   pushAt 1416 2 9344,
   opAt 1417 .MLOAD,
   opAt 1418 .ADD,
   pushAt 1419 1 32,
   opAt 1420 (.Swap ⟨0, by decide⟩),
   opAt 1421 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
