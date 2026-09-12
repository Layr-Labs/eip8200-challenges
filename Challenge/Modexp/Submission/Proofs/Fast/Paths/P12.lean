import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1627..1682). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1627..1661, pc 2257..2634. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1328 .JUMPDEST,
   opAt 1329 (.Dup ⟨1, by decide⟩),
   opAt 1330 .MLOAD,
   opAt 1331 (.Dup ⟨3, by decide⟩),
   opAt 1332 .MLOAD,
   opAt 1333 (.Dup ⟨1, by decide⟩),
   opAt 1334 .ADD,
   opAt 1335 (.Swap ⟨0, by decide⟩),
   opAt 1336 (.Dup ⟨1, by decide⟩),
   opAt 1337 .LT,
   opAt 1338 (.Swap ⟨0, by decide⟩),
   opAt 1339 (.Dup ⟨5, by decide⟩),
   opAt 1340 .ADD,
   opAt 1341 (.Swap ⟨4, by decide⟩),
   opAt 1342 (.Dup ⟨5, by decide⟩),
   opAt 1343 .LT,
   opAt 1344 .OR,
   opAt 1345 (.Swap ⟨3, by decide⟩),
   opAt 1346 (.Dup ⟨1, by decide⟩),
   opAt 1347 .MSTORE,
   pushAt 1348 1 31,
   opAt 1349 .NOT,
   opAt 1350 .ADD,
   opAt 1351 (.Swap ⟨0, by decide⟩),
   pushAt 1352 1 31,
   opAt 1353 .NOT,
   opAt 1354 .ADD,
   opAt 1355 (.Swap ⟨0, by decide⟩),
   opAt 1356 (.Swap ⟨1, by decide⟩),
   pushAt 1357 1 31,
   opAt 1358 .NOT,
   opAt 1359 .ADD,
   opAt 1360 (.Swap ⟨1, by decide⟩),
   pushAt 1361 2 8224,
   opAt 1362 (.Dup ⟨1, by decide⟩),
   opAt 1363 .GT,
   pushAt 1364 2 1796,
   opAt 1365 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2308. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1366 .POP,
   opAt 1367 .POP,
   opAt 1368 .POP,
   pushAt 1369 2 8224,
   opAt 1370 .MSTORE,

   pushAt 1371 2 4536,
   opAt 1372 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
