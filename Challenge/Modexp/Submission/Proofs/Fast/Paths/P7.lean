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
  [opAt 1363 .JUMPDEST,
   pushAt 1364 1 1,
   opAt 1365 (.Swap ⟨0, by decide⟩),
   opAt 1366 .SUB,
   opAt 1367 (.Dup ⟨0, by decide⟩),
   pushAt 1368 2 1906,
   opAt 1369 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1370 .POP,
   opAt 1371 .POP,
   opAt 1372 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1373 .JUMPDEST,
   pushAt 1374 2 9344,
   opAt 1375 .MLOAD,
   opAt 1376 (.Dup ⟨0, by decide⟩),
   pushAt 1377 1 64,
   opAt 1378 .ADD,
   opAt 1379 .CALLDATASIZE,
   pushAt 1380 2 8192,
   opAt 1381 .CALLDATACOPY,
   opAt 1382 (.Dup ⟨0, by decide⟩),
   opAt 1383 (.Dup ⟨3, by decide⟩),
   opAt 1384 .ADD,
   pushAt 1385 1 32,
   opAt 1386 (.Swap ⟨0, by decide⟩),
   opAt 1387 .SUB,
   pushAt 1388 1 32,
   opAt 1389 (.Dup ⟨4, by decide⟩),
   opAt 1390 .SUB,
   opAt 1391 (.Swap ⟨3, by decide⟩),
   opAt 1392 .POP,
   opAt 1393 (.Swap ⟨0, by decide⟩),
   opAt 1394 .POP,
   pushAt 1395 1 32,
   opAt 1396 (.Dup ⟨2, by decide⟩),
   opAt 1397 .SUB,
   opAt 1398 (.Swap ⟨1, by decide⟩),
   opAt 1399 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1400 .JUMPDEST,
   opAt 1401 (.Dup ⟨0, by decide⟩),
   opAt 1402 .MLOAD,
   pushAt 1403 0 0,
   pushAt 1404 2 9440,
   opAt 1405 .MLOAD,
   opAt 1406 (.Dup ⟨4, by decide⟩),
   pushAt 1407 2 9344,
   opAt 1408 .MLOAD,
   opAt 1409 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
