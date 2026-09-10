import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1421..1468). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1421..1468, pc 1995..2049. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1326 .JUMPDEST,
   opAt 1327 (.Dup ⟨3, by decide⟩),
   opAt 1328 (.Dup ⟨1, by decide⟩),
   opAt 1329 .MLOAD,
   opAt 1330 (.Dup ⟨1, by decide⟩),
   opAt 1331 (.Dup ⟨1, by decide⟩),
   opAt 1332 .MUL,
   opAt 1333 (.Swap ⟨1, by decide⟩),
   pushAt 1334 0 0,
   opAt 1335 .NOT,
   opAt 1336 (.Swap ⟨1, by decide⟩),
   opAt 1337 .MULMOD,
   opAt 1338 (.Dup ⟨1, by decide⟩),
   opAt 1339 (.Dup ⟨1, by decide⟩),
   opAt 1340 .LT,
   opAt 1341 (.Dup ⟨2, by decide⟩),
   opAt 1342 .ADD,
   opAt 1343 (.Swap ⟨0, by decide⟩),
   opAt 1344 .SUB,
   opAt 1345 (.Dup ⟨3, by decide⟩),
   opAt 1346 .MLOAD,
   opAt 1347 (.Swap ⟨1, by decide⟩),
   opAt 1348 (.Dup ⟨2, by decide⟩),
   opAt 1349 .ADD,
   opAt 1350 (.Swap ⟨1, by decide⟩),
   opAt 1351 (.Dup ⟨2, by decide⟩),
   opAt 1352 .LT,
   opAt 1353 .ADD,
   opAt 1354 (.Swap ⟨0, by decide⟩),
   opAt 1355 (.Dup ⟨4, by decide⟩),
   opAt 1356 .ADD,
   opAt 1357 (.Swap ⟨3, by decide⟩),
   opAt 1358 (.Dup ⟨4, by decide⟩),
   opAt 1359 .LT,
   opAt 1360 .ADD,
   opAt 1361 (.Swap ⟨2, by decide⟩),
   opAt 1362 (.Dup ⟨2, by decide⟩),
   opAt 1363 .MSTORE,
   pushAt 1364 1 31,
   opAt 1365 .NOT,
   opAt 1366 .ADD,
   opAt 1367 (.Swap ⟨0, by decide⟩),
   pushAt 1368 1 31,
   opAt 1369 .NOT,
   opAt 1370 .ADD,
   opAt 1371 (.Swap ⟨0, by decide⟩),
   opAt 1372 (.Dup ⟨5, by decide⟩),
   opAt 1373 (.Dup ⟨1, by decide⟩),
   opAt 1374 .GT,
   pushAt 1375 2 1833,
   opAt 1376 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
