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
  [opAt 1361 .JUMPDEST,
   pushAt 1362 1 1,
   opAt 1363 (.Swap ⟨0, by decide⟩),
   opAt 1364 .SUB,
   opAt 1365 (.Dup ⟨0, by decide⟩),
   pushAt 1366 2 1884,
   opAt 1367 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1368 .POP,
   opAt 1369 .POP,
   opAt 1370 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1371 .JUMPDEST,
   pushAt 1372 2 9344,
   opAt 1373 .MLOAD,
   opAt 1374 (.Dup ⟨0, by decide⟩),
   pushAt 1375 1 64,
   opAt 1376 .ADD,
   opAt 1377 .CALLDATASIZE,
   pushAt 1378 2 8192,
   opAt 1379 .CALLDATACOPY,
   opAt 1380 (.Dup ⟨0, by decide⟩),
   opAt 1381 (.Dup ⟨3, by decide⟩),
   opAt 1382 .ADD,
   pushAt 1383 1 32,
   opAt 1384 (.Swap ⟨0, by decide⟩),
   opAt 1385 .SUB,
   pushAt 1386 1 32,
   opAt 1387 (.Dup ⟨4, by decide⟩),
   opAt 1388 .SUB,
   opAt 1389 (.Swap ⟨3, by decide⟩),
   opAt 1390 .POP,
   opAt 1391 (.Swap ⟨0, by decide⟩),
   opAt 1392 .POP,
   pushAt 1393 1 32,
   opAt 1394 (.Dup ⟨2, by decide⟩),
   opAt 1395 .SUB,
   opAt 1396 (.Swap ⟨1, by decide⟩),
   opAt 1397 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1398 .JUMPDEST,
   opAt 1399 (.Dup ⟨0, by decide⟩),
   opAt 1400 .MLOAD,
   pushAt 1401 0 0,
   pushAt 1402 4 9440,
   opAt 1403 .MLOAD,
   opAt 1404 (.Dup ⟨4, by decide⟩),
   pushAt 1405 7 9344,
   opAt 1406 .MLOAD,
   opAt 1407 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
