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
  [opAt 1328 .JUMPDEST,
   opAt 1329 (.Dup ⟨0, by decide⟩),
   opAt 1330 .MLOAD,
   pushAt 1331 0 0,
   opAt 1332 .NOT,
   opAt 1333 (.Dup ⟨5, by decide⟩),
   opAt 1334 (.Dup ⟨2, by decide⟩),
   opAt 1335 .MUL,
   opAt 1336 (.Swap ⟨1, by decide⟩),
   opAt 1337 (.Dup ⟨6, by decide⟩),
   opAt 1338 .MULMOD,
   opAt 1339 (.Dup ⟨1, by decide⟩),
   opAt 1340 (.Dup ⟨1, by decide⟩),
   opAt 1341 .LT,
   opAt 1342 .SUB,
   opAt 1343 (.Dup ⟨4, by decide⟩),
   opAt 1344 (.Dup ⟨2, by decide⟩),
   opAt 1345 .ADD,
   opAt 1346 (.Dup ⟨0, by decide⟩),
   opAt 1347 (.Swap ⟨5, by decide⟩),
   opAt 1348 .GT,
   opAt 1349 .SUB,
   opAt 1350 .SUB,
   opAt 1351 (.Dup ⟨3, by decide⟩),
   opAt 1352 (.Dup ⟨3, by decide⟩),
   opAt 1353 .MLOAD,
   opAt 1354 .ADD,
   opAt 1355 (.Dup ⟨0, by decide⟩),
   opAt 1356 (.Swap ⟨4, by decide⟩),
   opAt 1357 .GT,
   opAt 1358 .ADD,
   opAt 1359 (.Swap ⟨2, by decide⟩),
   pushAt 1360 1 32,
   opAt 1361 (.Dup ⟨3, by decide⟩),
   pushAt 1362 1 31,
   opAt 1363 .NOT,
   opAt 1364 .ADD,
   opAt 1365 (.Swap ⟨3, by decide⟩),
   opAt 1366 .ADD,
   opAt 1367 .MSTORE,
   pushAt 1368 1 31,
   opAt 1369 .NOT,
   opAt 1370 .ADD,
   pushAt 1371 2 2080,
   opAt 1372 (.Dup ⟨2, by decide⟩),
   opAt 1373 .GT,
   pushAt 1374 2 1799,
   opAt 1375 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
