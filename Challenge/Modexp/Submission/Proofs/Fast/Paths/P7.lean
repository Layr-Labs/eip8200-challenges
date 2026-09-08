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
  [opAt 1360 .JUMPDEST,
   pushAt 1361 1 1,
   opAt 1362 (.Swap ⟨0, by decide⟩),
   opAt 1363 .SUB,
   opAt 1364 (.Dup ⟨0, by decide⟩),
   pushAt 1365 2 1906,
   opAt 1366 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1367 .POP,
   opAt 1368 .POP,
   opAt 1369 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1370 .JUMPDEST,
   pushAt 1371 2 9344,
   opAt 1372 .MLOAD,
   opAt 1373 (.Dup ⟨0, by decide⟩),
   pushAt 1374 1 64,
   opAt 1375 .ADD,
   opAt 1376 .CALLDATASIZE,
   pushAt 1377 2 8192,
   opAt 1378 .CALLDATACOPY,
   opAt 1379 (.Dup ⟨0, by decide⟩),
   opAt 1380 (.Dup ⟨3, by decide⟩),
   opAt 1381 .ADD,
   pushAt 1382 1 32,
   opAt 1383 (.Swap ⟨0, by decide⟩),
   opAt 1384 .SUB,
   pushAt 1385 1 32,
   opAt 1386 (.Dup ⟨4, by decide⟩),
   opAt 1387 .SUB,
   opAt 1388 (.Swap ⟨3, by decide⟩),
   opAt 1389 .POP,
   opAt 1390 (.Swap ⟨0, by decide⟩),
   opAt 1391 .POP,
   pushAt 1392 1 32,
   opAt 1393 (.Dup ⟨2, by decide⟩),
   opAt 1394 .SUB,
   opAt 1395 (.Swap ⟨1, by decide⟩),
   opAt 1396 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1397 .JUMPDEST,
   opAt 1398 (.Dup ⟨0, by decide⟩),
   opAt 1399 .MLOAD,
   pushAt 1400 0 0,
   pushAt 1401 4 9440,
   opAt 1402 .MLOAD,
   opAt 1403 (.Dup ⟨4, by decide⟩),
   pushAt 1404 7 9344,
   opAt 1405 .MLOAD,
   opAt 1406 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
