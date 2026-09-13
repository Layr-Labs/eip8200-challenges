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
  [opAt 1345 .POP,
   opAt 1346 .POP,
   opAt 1347 (.Dup ⟨0, by decide⟩),
   pushAt 1348 2 2080,
   opAt 1349 .MLOAD,
   opAt 1350 .ADD,
   opAt 1351 (.Dup ⟨0, by decide⟩),
   pushAt 1352 2 2080,
   opAt 1353 .MSTORE,
   opAt 1354 .LT,
   pushAt 1355 2 2048,
   opAt 1356 .MSTORE,
   pushAt 1357 2 2784,
   opAt 1358 .MLOAD,
   opAt 1359 .MLOAD,
   pushAt 1360 2 2720,
   opAt 1361 .MLOAD,
   opAt 1362 .MUL,
   opAt 1363 (.Dup ⟨0, by decide⟩),
   pushAt 1364 2 2752,
   opAt 1365 .MLOAD,
   opAt 1366 .MLOAD,
   opAt 1367 (.Dup ⟨1, by decide⟩),
   opAt 1368 (.Dup ⟨1, by decide⟩),
   opAt 1369 .MUL,
   opAt 1370 (.Swap ⟨1, by decide⟩),
   pushAt 1371 0 0,
   opAt 1372 .NOT,
   opAt 1373 (.Swap ⟨1, by decide⟩),
   opAt 1374 .MULMOD,
   opAt 1375 (.Dup ⟨1, by decide⟩),
   opAt 1376 (.Dup ⟨1, by decide⟩),
   opAt 1377 .LT,
   opAt 1378 (.Dup ⟨2, by decide⟩),
   opAt 1379 .ADD,
   opAt 1380 (.Swap ⟨0, by decide⟩),
   opAt 1381 .SUB,
   opAt 1382 (.Swap ⟨0, by decide⟩),
   pushAt 1383 0 0,
   opAt 1384 .LT,
   opAt 1385 .ADD,
   pushAt 1386 2 2784,
   opAt 1387 .MLOAD,
   pushAt 1388 1 32,
   opAt 1389 (.Swap ⟨0, by decide⟩),
   opAt 1390 .SUB,
   pushAt 1391 2 2752,
   opAt 1392 .MLOAD,
   pushAt 1393 1 32,
   opAt 1394 (.Swap ⟨0, by decide⟩),
   opAt 1395 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
