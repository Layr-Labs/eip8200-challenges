import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1599..1600). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1599..1600, pc 2175..2243. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1347 .POP,
   opAt 1348 .POP,
   opAt 1349 (.Dup ⟨0, by decide⟩),
   pushAt 1350 2 4128,
   opAt 1351 .MLOAD,
   opAt 1352 .ADD,
   opAt 1353 (.Dup ⟨0, by decide⟩),
   pushAt 1354 2 4128,
   opAt 1355 .MSTORE,
   opAt 1356 .LT,
   pushAt 1357 2 4096,
   opAt 1358 .MSTORE,
   pushAt 1359 2 5344,
   opAt 1360 .MLOAD,
   opAt 1361 .MLOAD,
   pushAt 1362 2 5280,
   opAt 1363 .MLOAD,
   opAt 1364 .MUL,
   opAt 1365 (.Dup ⟨0, by decide⟩),
   pushAt 1366 2 5312,
   opAt 1367 .MLOAD,
   opAt 1368 .MLOAD,
   opAt 1369 (.Dup ⟨1, by decide⟩),
   opAt 1370 (.Dup ⟨1, by decide⟩),
   opAt 1371 .MUL,
   opAt 1372 (.Swap ⟨1, by decide⟩),
   pushAt 1373 0 0,
   opAt 1374 .NOT,
   opAt 1375 (.Swap ⟨1, by decide⟩),
   opAt 1376 .MULMOD,
   opAt 1377 (.Dup ⟨1, by decide⟩),
   opAt 1378 (.Dup ⟨1, by decide⟩),
   opAt 1379 .LT,
   opAt 1380 (.Dup ⟨2, by decide⟩),
   opAt 1381 .ADD,
   opAt 1382 (.Swap ⟨0, by decide⟩),
   opAt 1383 .SUB,
   opAt 1384 (.Swap ⟨0, by decide⟩),
   pushAt 1385 0 0,
   opAt 1386 .LT,
   opAt 1387 .ADD,
   pushAt 1388 2 5344,
   opAt 1389 .MLOAD,
   pushAt 1390 1 32,
   opAt 1391 (.Swap ⟨0, by decide⟩),
   opAt 1392 .SUB,
   pushAt 1393 2 5312,
   opAt 1394 .MLOAD,
   pushAt 1395 1 32,
   opAt 1396 (.Swap ⟨0, by decide⟩),
   opAt 1397 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
