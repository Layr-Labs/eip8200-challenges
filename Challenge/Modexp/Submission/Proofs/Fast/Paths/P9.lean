import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1599..1600). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1599..1600, pc 2180..2248. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1350 .POP,
   opAt 1351 .POP,
   opAt 1352 (.Dup ⟨0, by decide⟩),
   pushAt 1353 2 4128,
   opAt 1354 .MLOAD,
   opAt 1355 .ADD,
   opAt 1356 (.Dup ⟨0, by decide⟩),
   pushAt 1357 2 4128,
   opAt 1358 .MSTORE,
   opAt 1359 .LT,
   pushAt 1360 2 4096,
   opAt 1361 .MSTORE,
   pushAt 1362 2 5344,
   opAt 1363 .MLOAD,
   opAt 1364 .MLOAD,
   pushAt 1365 2 5280,
   opAt 1366 .MLOAD,
   opAt 1367 .MUL,
   opAt 1368 (.Dup ⟨0, by decide⟩),
   pushAt 1369 2 5312,
   opAt 1370 .MLOAD,
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
   opAt 1387 (.Swap ⟨0, by decide⟩),
   pushAt 1388 0 0,
   opAt 1389 .LT,
   opAt 1390 .ADD,
   pushAt 1391 2 5344,
   opAt 1392 .MLOAD,
   pushAt 1393 1 32,
   opAt 1394 (.Swap ⟨0, by decide⟩),
   opAt 1395 .SUB,
   pushAt 1396 2 5312,
   opAt 1397 .MLOAD,
   pushAt 1398 1 32,
   opAt 1399 (.Swap ⟨0, by decide⟩),
   opAt 1400 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
