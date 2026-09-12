import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1567..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1567..1568, pc 2119..2226. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1363 .JUMPDEST,
   opAt 1364 (.Dup ⟨0, by decide⟩),
   opAt 1365 .MLOAD,
   pushAt 1366 0 0,
   opAt 1367 .NOT,
   opAt 1368 (.Dup ⟨5, by decide⟩),
   opAt 1369 (.Dup ⟨2, by decide⟩),
   opAt 1370 .MUL,
   opAt 1371 (.Swap ⟨1, by decide⟩),
   opAt 1372 (.Dup ⟨6, by decide⟩),
   opAt 1373 .MULMOD,
   opAt 1374 (.Dup ⟨1, by decide⟩),
   opAt 1375 (.Dup ⟨1, by decide⟩),
   opAt 1376 .LT,
   opAt 1377 .SUB,
   opAt 1378 (.Dup ⟨4, by decide⟩),
   opAt 1379 (.Dup ⟨2, by decide⟩),
   opAt 1380 .ADD,
   opAt 1381 (.Dup ⟨0, by decide⟩),
   opAt 1382 (.Swap ⟨5, by decide⟩),
   opAt 1383 .GT,
   opAt 1384 .SUB,
   opAt 1385 .SUB,
   opAt 1386 (.Dup ⟨3, by decide⟩),
   opAt 1387 (.Dup ⟨3, by decide⟩),
   opAt 1388 .MLOAD,
   opAt 1389 .ADD,
   opAt 1390 (.Dup ⟨0, by decide⟩),
   opAt 1391 (.Swap ⟨4, by decide⟩),
   opAt 1392 .GT,
   opAt 1393 .ADD,
   opAt 1394 (.Swap ⟨2, by decide⟩),
   pushAt 1395 1 32,
   opAt 1396 (.Dup ⟨3, by decide⟩),
   pushAt 1397 1 31,
   opAt 1398 .NOT,
   opAt 1399 .ADD,
   opAt 1400 (.Swap ⟨3, by decide⟩),
   opAt 1401 .ADD,
   opAt 1402 .MSTORE,
   pushAt 1403 1 31,
   opAt 1404 .NOT,
   opAt 1405 .ADD,
   pushAt 1406 2 8224,
   opAt 1407 (.Dup ⟨2, by decide⟩),
   opAt 1408 .GT,
   pushAt 1409 2 1847,
   opAt 1410 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
