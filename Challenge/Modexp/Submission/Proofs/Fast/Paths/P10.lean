import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1519..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1519..1568, pc 2119..2178. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1352 .JUMPDEST,
   opAt 1353 (.Dup ⟨0, by decide⟩),
   opAt 1354 .MLOAD,
   pushAt 1355 0 0,
   opAt 1356 .NOT,
   opAt 1357 (.Dup ⟨5, by decide⟩),
   opAt 1358 (.Dup ⟨2, by decide⟩),
   opAt 1359 .MUL,
   opAt 1360 (.Swap ⟨1, by decide⟩),
   opAt 1361 (.Dup ⟨6, by decide⟩),
   opAt 1362 .MULMOD,
   opAt 1363 (.Dup ⟨1, by decide⟩),
   opAt 1364 (.Dup ⟨1, by decide⟩),
   opAt 1365 .LT,
   opAt 1366 .SUB,
   opAt 1367 (.Dup ⟨4, by decide⟩),
   opAt 1368 (.Dup ⟨2, by decide⟩),
   opAt 1369 .ADD,
   opAt 1370 (.Dup ⟨0, by decide⟩),
   opAt 1371 (.Swap ⟨5, by decide⟩),
   opAt 1372 .GT,
   opAt 1373 .SUB,
   opAt 1374 .SUB,
   opAt 1375 (.Dup ⟨3, by decide⟩),
   opAt 1376 (.Dup ⟨3, by decide⟩),
   opAt 1377 .MLOAD,
   opAt 1378 .ADD,
   opAt 1379 (.Dup ⟨0, by decide⟩),
   opAt 1380 (.Swap ⟨4, by decide⟩),
   opAt 1381 .GT,
   opAt 1382 .ADD,
   opAt 1383 (.Swap ⟨2, by decide⟩),
   pushAt 1384 1 32,
   opAt 1385 (.Dup ⟨3, by decide⟩),
   pushAt 1386 1 31,
   opAt 1387 .NOT,
   opAt 1388 .ADD,
   opAt 1389 (.Swap ⟨3, by decide⟩),
   opAt 1390 .ADD,
   opAt 1391 .MSTORE,
   pushAt 1392 1 31,
   opAt 1393 .NOT,
   opAt 1394 .ADD,
   pushAt 1395 2 8224,
   opAt 1396 (.Dup ⟨2, by decide⟩),
   opAt 1397 .GT,
   pushAt 1398 2 1840,
   opAt 1399 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
