import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1469..1518). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1469..1518, pc 2050..2118. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1377 .POP,
   opAt 1378 .POP,
   opAt 1379 (.Dup ⟨0, by decide⟩),
   pushAt 1380 2 8224,
   opAt 1381 .MLOAD,
   opAt 1382 .ADD,
   opAt 1383 (.Dup ⟨0, by decide⟩),
   pushAt 1384 2 8224,
   opAt 1385 .MSTORE,
   opAt 1386 .LT,
   pushAt 1387 2 8192,
   opAt 1388 .MSTORE,
   pushAt 1389 2 9440,
   opAt 1390 .MLOAD,
   opAt 1391 .MLOAD,
   pushAt 1392 2 9376,
   opAt 1393 .MLOAD,
   opAt 1394 .MUL,
   opAt 1395 (.Dup ⟨0, by decide⟩),
   pushAt 1396 2 9408,
   opAt 1397 .MLOAD,
   opAt 1398 .MLOAD,
   opAt 1399 (.Dup ⟨1, by decide⟩),
   opAt 1400 (.Dup ⟨1, by decide⟩),
   opAt 1401 .MUL,
   opAt 1402 (.Swap ⟨1, by decide⟩),
   pushAt 1403 0 0,
   opAt 1404 .NOT,
   opAt 1405 (.Swap ⟨1, by decide⟩),
   opAt 1406 .MULMOD,
   opAt 1407 (.Dup ⟨1, by decide⟩),
   opAt 1408 (.Dup ⟨1, by decide⟩),
   opAt 1409 .LT,
   opAt 1410 (.Dup ⟨2, by decide⟩),
   opAt 1411 .ADD,
   opAt 1412 (.Swap ⟨0, by decide⟩),
   opAt 1413 .SUB,
   opAt 1414 (.Swap ⟨0, by decide⟩),
   pushAt 1415 0 0,
   opAt 1416 .LT,
   opAt 1417 .ADD,
   pushAt 1418 2 9440,
   opAt 1419 .MLOAD,
   pushAt 1420 1 32,
   opAt 1421 (.Swap ⟨0, by decide⟩),
   opAt 1422 .SUB,
   pushAt 1423 2 9408,
   opAt 1424 .MLOAD,
   pushAt 1425 1 32,
   opAt 1426 (.Swap ⟨0, by decide⟩),
   opAt 1427 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
