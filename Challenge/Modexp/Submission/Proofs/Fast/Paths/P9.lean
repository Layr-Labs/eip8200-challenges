import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1517..1518). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1517..1518, pc 2098..2166. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1312 .POP,
   opAt 1313 .POP,
   opAt 1314 (.Dup ⟨0, by decide⟩),
   pushAt 1315 2 8224,
   opAt 1316 .MLOAD,
   opAt 1317 .ADD,
   opAt 1318 (.Dup ⟨0, by decide⟩),
   pushAt 1319 2 8224,
   opAt 1320 .MSTORE,
   opAt 1321 .LT,
   pushAt 1322 2 8192,
   opAt 1323 .MSTORE,
   pushAt 1324 2 9440,
   opAt 1325 .MLOAD,
   opAt 1326 .MLOAD,
   pushAt 1327 2 9376,
   opAt 1328 .MLOAD,
   opAt 1329 .MUL,
   opAt 1330 (.Dup ⟨0, by decide⟩),
   pushAt 1331 2 9408,
   opAt 1332 .MLOAD,
   opAt 1333 .MLOAD,
   opAt 1334 (.Dup ⟨1, by decide⟩),
   opAt 1335 (.Dup ⟨1, by decide⟩),
   opAt 1336 .MUL,
   opAt 1337 (.Swap ⟨1, by decide⟩),
   pushAt 1338 0 0,
   opAt 1339 .NOT,
   opAt 1340 (.Swap ⟨1, by decide⟩),
   opAt 1341 .MULMOD,
   opAt 1342 (.Dup ⟨1, by decide⟩),
   opAt 1343 (.Dup ⟨1, by decide⟩),
   opAt 1344 .LT,
   opAt 1345 (.Dup ⟨2, by decide⟩),
   opAt 1346 .ADD,
   opAt 1347 (.Swap ⟨0, by decide⟩),
   opAt 1348 .SUB,
   opAt 1349 (.Swap ⟨0, by decide⟩),
   pushAt 1350 0 0,
   opAt 1351 .LT,
   opAt 1352 .ADD,
   pushAt 1353 2 9440,
   opAt 1354 .MLOAD,
   pushAt 1355 1 32,
   opAt 1356 (.Swap ⟨0, by decide⟩),
   opAt 1357 .SUB,
   pushAt 1358 2 9408,
   opAt 1359 .MLOAD,
   pushAt 1360 1 32,
   opAt 1361 (.Swap ⟨0, by decide⟩),
   opAt 1362 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
