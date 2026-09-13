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
  [opAt 1344 .POP,
   opAt 1345 .POP,
   opAt 1346 (.Dup ⟨0, by decide⟩),
   pushAt 1347 2 2080,
   opAt 1348 .MLOAD,
   opAt 1349 .ADD,
   opAt 1350 (.Dup ⟨0, by decide⟩),
   pushAt 1351 2 2080,
   opAt 1352 .MSTORE,
   opAt 1353 .LT,
   pushAt 1354 2 2048,
   opAt 1355 .MSTORE,
   pushAt 1356 2 2784,
   opAt 1357 .MLOAD,
   opAt 1358 .MLOAD,
   pushAt 1359 2 2720,
   opAt 1360 .MLOAD,
   opAt 1361 .MUL,
   opAt 1362 (.Dup ⟨0, by decide⟩),
   pushAt 1363 2 2752,
   opAt 1364 .MLOAD,
   opAt 1365 .MLOAD,
   opAt 1366 (.Dup ⟨1, by decide⟩),
   opAt 1367 (.Dup ⟨1, by decide⟩),
   opAt 1368 .MUL,
   opAt 1369 (.Swap ⟨1, by decide⟩),
   pushAt 1370 0 0,
   opAt 1371 .NOT,
   opAt 1372 (.Swap ⟨1, by decide⟩),
   opAt 1373 .MULMOD,
   opAt 1374 (.Dup ⟨1, by decide⟩),
   opAt 1375 (.Dup ⟨1, by decide⟩),
   opAt 1376 .LT,
   opAt 1377 (.Dup ⟨2, by decide⟩),
   opAt 1378 .ADD,
   opAt 1379 (.Swap ⟨0, by decide⟩),
   opAt 1380 .SUB,
   opAt 1381 (.Swap ⟨0, by decide⟩),
   pushAt 1382 0 0,
   opAt 1383 .LT,
   opAt 1384 .ADD,
   pushAt 1385 2 2784,
   opAt 1386 .MLOAD,
   pushAt 1387 1 32,
   opAt 1388 (.Swap ⟨0, by decide⟩),
   opAt 1389 .SUB,
   pushAt 1390 2 2752,
   opAt 1391 .MLOAD,
   pushAt 1392 1 32,
   opAt 1393 (.Swap ⟨0, by decide⟩),
   opAt 1394 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
