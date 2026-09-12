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
  [opAt 1326 .JUMPDEST,
   opAt 1327 (.Dup ⟨0, by decide⟩),
   opAt 1328 .MLOAD,
   pushAt 1329 0 0,
   opAt 1330 .NOT,
   opAt 1331 (.Dup ⟨5, by decide⟩),
   opAt 1332 (.Dup ⟨2, by decide⟩),
   opAt 1333 .MUL,
   opAt 1334 (.Swap ⟨1, by decide⟩),
   opAt 1335 (.Dup ⟨6, by decide⟩),
   opAt 1336 .MULMOD,
   opAt 1337 (.Dup ⟨1, by decide⟩),
   opAt 1338 (.Dup ⟨1, by decide⟩),
   opAt 1339 .LT,
   opAt 1340 .SUB,
   opAt 1341 (.Dup ⟨4, by decide⟩),
   opAt 1342 (.Dup ⟨2, by decide⟩),
   opAt 1343 .ADD,
   opAt 1344 (.Dup ⟨0, by decide⟩),
   opAt 1345 (.Swap ⟨5, by decide⟩),
   opAt 1346 .GT,
   opAt 1347 .SUB,
   opAt 1348 .SUB,
   opAt 1349 (.Dup ⟨3, by decide⟩),
   opAt 1350 (.Dup ⟨3, by decide⟩),
   opAt 1351 .MLOAD,
   opAt 1352 .ADD,
   opAt 1353 (.Dup ⟨0, by decide⟩),
   opAt 1354 (.Swap ⟨4, by decide⟩),
   opAt 1355 .GT,
   opAt 1356 .ADD,
   opAt 1357 (.Swap ⟨2, by decide⟩),
   pushAt 1358 1 32,
   opAt 1359 (.Dup ⟨3, by decide⟩),
   pushAt 1360 1 31,
   opAt 1361 .NOT,
   opAt 1362 .ADD,
   opAt 1363 (.Swap ⟨3, by decide⟩),
   opAt 1364 .ADD,
   opAt 1365 .MSTORE,
   pushAt 1366 1 31,
   opAt 1367 .NOT,
   opAt 1368 .ADD,
   pushAt 1369 2 8224,
   opAt 1370 (.Dup ⟨2, by decide⟩),
   opAt 1371 .GT,
   pushAt 1372 2 1795,
   opAt 1373 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
