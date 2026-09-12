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
  [opAt 1333 .JUMPDEST,
   opAt 1334 (.Dup ⟨0, by decide⟩),
   opAt 1335 .MLOAD,
   pushAt 1336 0 0,
   opAt 1337 .NOT,
   opAt 1338 (.Dup ⟨5, by decide⟩),
   opAt 1339 (.Dup ⟨2, by decide⟩),
   opAt 1340 .MUL,
   opAt 1341 (.Swap ⟨1, by decide⟩),
   opAt 1342 (.Dup ⟨6, by decide⟩),
   opAt 1343 .MULMOD,
   opAt 1344 (.Dup ⟨1, by decide⟩),
   opAt 1345 (.Dup ⟨1, by decide⟩),
   opAt 1346 .LT,
   opAt 1347 .SUB,
   opAt 1348 (.Dup ⟨4, by decide⟩),
   opAt 1349 (.Dup ⟨2, by decide⟩),
   opAt 1350 .ADD,
   opAt 1351 (.Dup ⟨0, by decide⟩),
   opAt 1352 (.Swap ⟨5, by decide⟩),
   opAt 1353 .GT,
   opAt 1354 .SUB,
   opAt 1355 .SUB,
   opAt 1356 (.Dup ⟨3, by decide⟩),
   opAt 1357 (.Dup ⟨3, by decide⟩),
   opAt 1358 .MLOAD,
   opAt 1359 .ADD,
   opAt 1360 (.Dup ⟨0, by decide⟩),
   opAt 1361 (.Swap ⟨4, by decide⟩),
   opAt 1362 .GT,
   opAt 1363 .ADD,
   opAt 1364 (.Swap ⟨2, by decide⟩),
   pushAt 1365 1 32,
   opAt 1366 (.Dup ⟨3, by decide⟩),
   pushAt 1367 1 31,
   opAt 1368 .NOT,
   opAt 1369 .ADD,
   opAt 1370 (.Swap ⟨3, by decide⟩),
   opAt 1371 .ADD,
   opAt 1372 .MSTORE,
   pushAt 1373 1 31,
   opAt 1374 .NOT,
   opAt 1375 .ADD,
   pushAt 1376 2 8224,
   opAt 1377 (.Dup ⟨2, by decide⟩),
   opAt 1378 .GT,
   pushAt 1379 2 1811,
   opAt 1380 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
