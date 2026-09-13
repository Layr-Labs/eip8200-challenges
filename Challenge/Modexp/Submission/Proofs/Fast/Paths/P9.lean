import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1599..1600). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1599..1600, pc 2177..2245. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1349 .POP,
   opAt 1350 .POP,
   opAt 1351 (.Dup ⟨0, by decide⟩),
   pushAt 1352 2 2080,
   opAt 1353 .MLOAD,
   opAt 1354 .ADD,
   opAt 1355 (.Dup ⟨0, by decide⟩),
   pushAt 1356 2 2080,
   opAt 1357 .MSTORE,
   opAt 1358 .LT,
   pushAt 1359 2 2048,
   opAt 1360 .MSTORE,
   pushAt 1361 2 2784,
   opAt 1362 .MLOAD,
   opAt 1363 .MLOAD,
   pushAt 1364 2 2720,
   opAt 1365 .MLOAD,
   opAt 1366 .MUL,
   opAt 1367 (.Dup ⟨0, by decide⟩),
   pushAt 1368 2 2752,
   opAt 1369 .MLOAD,
   opAt 1370 .MLOAD,
   opAt 1371 (.Dup ⟨1, by decide⟩),
   opAt 1372 (.Dup ⟨1, by decide⟩),
   opAt 1373 .MUL,
   opAt 1374 (.Swap ⟨1, by decide⟩),
   pushAt 1375 0 0,
   opAt 1376 .NOT,
   opAt 1377 (.Swap ⟨1, by decide⟩),
   opAt 1378 .MULMOD,
   opAt 1379 (.Dup ⟨1, by decide⟩),
   opAt 1380 (.Dup ⟨1, by decide⟩),
   opAt 1381 .LT,
   opAt 1382 (.Dup ⟨2, by decide⟩),
   opAt 1383 .ADD,
   opAt 1384 (.Swap ⟨0, by decide⟩),
   opAt 1385 .SUB,
   opAt 1386 (.Swap ⟨0, by decide⟩),
   pushAt 1387 0 0,
   opAt 1388 .LT,
   opAt 1389 .ADD,
   pushAt 1390 2 2784,
   opAt 1391 .MLOAD,
   pushAt 1392 1 32,
   opAt 1393 (.Swap ⟨0, by decide⟩),
   opAt 1394 .SUB,
   pushAt 1395 2 2752,
   opAt 1396 .MLOAD,
   pushAt 1397 1 32,
   opAt 1398 (.Swap ⟨0, by decide⟩),
   opAt 1399 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
