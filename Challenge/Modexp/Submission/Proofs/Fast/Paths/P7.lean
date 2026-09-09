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
  [opAt 1365 .JUMPDEST,
   pushAt 1366 1 1,
   opAt 1367 (.Swap ⟨0, by decide⟩),
   opAt 1368 .SUB,
   opAt 1369 (.Dup ⟨0, by decide⟩),
   pushAt 1370 2 1906,
   opAt 1371 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1372 .POP,
   opAt 1373 .POP,
   opAt 1374 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1375 .JUMPDEST,
   pushAt 1376 2 9344,
   opAt 1377 .MLOAD,
   opAt 1378 (.Dup ⟨0, by decide⟩),
   pushAt 1379 1 64,
   opAt 1380 .ADD,
   opAt 1381 .CALLDATASIZE,
   pushAt 1382 2 8192,
   opAt 1383 .CALLDATACOPY,
   opAt 1384 (.Dup ⟨0, by decide⟩),
   opAt 1385 (.Dup ⟨3, by decide⟩),
   opAt 1386 .ADD,
   pushAt 1387 1 32,
   opAt 1388 (.Swap ⟨0, by decide⟩),
   opAt 1389 .SUB,
   pushAt 1390 1 32,
   opAt 1391 (.Dup ⟨4, by decide⟩),
   opAt 1392 .SUB,
   opAt 1393 (.Swap ⟨3, by decide⟩),
   opAt 1394 .POP,
   opAt 1395 (.Swap ⟨0, by decide⟩),
   opAt 1396 .POP,
   pushAt 1397 1 32,
   opAt 1398 (.Dup ⟨2, by decide⟩),
   opAt 1399 .SUB,
   opAt 1400 (.Swap ⟨1, by decide⟩),
   opAt 1401 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1402 .JUMPDEST,
   opAt 1403 (.Dup ⟨0, by decide⟩),
   opAt 1404 .MLOAD,
   pushAt 1405 0 0,
   pushAt 1406 2 9440,
   opAt 1407 .MLOAD,
   opAt 1408 (.Dup ⟨4, by decide⟩),
   pushAt 1409 2 9344,
   opAt 1410 .MLOAD,
   opAt 1411 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
