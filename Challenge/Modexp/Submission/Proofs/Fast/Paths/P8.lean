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
  [opAt 1368 .JUMPDEST,
   opAt 1369 (.Dup ⟨3, by decide⟩),
   opAt 1370 (.Dup ⟨1, by decide⟩),
   opAt 1371 .MLOAD,
   opAt 1372 (.Dup ⟨1, by decide⟩),
   opAt 1373 (.Dup ⟨1, by decide⟩),
   opAt 1374 .MUL,
   opAt 1375 (.Swap ⟨1, by decide⟩),
   pushAt 1376 0 0,
   opAt 1377 .NOT,
   opAt 1378 (.Swap ⟨1, by decide⟩),
   opAt 1379 .MULMOD,
   opAt 1380 (.Dup ⟨1, by decide⟩),
   opAt 1381 (.Dup ⟨1, by decide⟩),
   opAt 1382 .LT,
   opAt 1383 (.Dup ⟨2, by decide⟩),
   opAt 1384 .ADD,
   opAt 1385 (.Swap ⟨0, by decide⟩),
   opAt 1386 .SUB,
   opAt 1387 (.Dup ⟨3, by decide⟩),
   opAt 1388 .MLOAD,
   opAt 1389 (.Swap ⟨1, by decide⟩),
   opAt 1390 (.Dup ⟨2, by decide⟩),
   opAt 1391 .ADD,
   opAt 1392 (.Swap ⟨1, by decide⟩),
   opAt 1393 (.Dup ⟨2, by decide⟩),
   opAt 1394 .LT,
   opAt 1395 .ADD,
   opAt 1396 (.Swap ⟨0, by decide⟩),
   opAt 1397 (.Dup ⟨4, by decide⟩),
   opAt 1398 .ADD,
   opAt 1399 (.Swap ⟨3, by decide⟩),
   opAt 1400 (.Dup ⟨4, by decide⟩),
   opAt 1401 .LT,
   opAt 1402 .ADD,
   opAt 1403 (.Swap ⟨2, by decide⟩),
   opAt 1404 (.Dup ⟨2, by decide⟩),
   opAt 1405 .MSTORE,
   pushAt 1406 1 31,
   opAt 1407 .NOT,
   opAt 1408 .ADD,
   opAt 1409 (.Swap ⟨0, by decide⟩),
   pushAt 1410 1 31,
   opAt 1411 .NOT,
   opAt 1412 .ADD,
   opAt 1413 (.Swap ⟨0, by decide⟩),
   opAt 1414 (.Dup ⟨5, by decide⟩),
   opAt 1415 (.Dup ⟨1, by decide⟩),
   opAt 1416 .GT,
   pushAt 1417 2 1914,
   opAt 1418 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
