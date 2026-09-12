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
  [opAt 1302 .JUMPDEST,
   opAt 1303 (.Dup ⟨3, by decide⟩),
   opAt 1304 (.Dup ⟨1, by decide⟩),
   opAt 1305 .MLOAD,
   opAt 1306 (.Dup ⟨1, by decide⟩),
   opAt 1307 (.Dup ⟨1, by decide⟩),
   opAt 1308 .MUL,
   opAt 1309 (.Swap ⟨1, by decide⟩),
   pushAt 1310 0 0,
   opAt 1311 .NOT,
   opAt 1312 (.Swap ⟨1, by decide⟩),
   opAt 1313 .MULMOD,
   opAt 1314 (.Dup ⟨1, by decide⟩),
   opAt 1315 (.Dup ⟨1, by decide⟩),
   opAt 1316 .LT,
   opAt 1317 (.Dup ⟨2, by decide⟩),
   opAt 1318 .ADD,
   opAt 1319 (.Swap ⟨0, by decide⟩),
   opAt 1320 .SUB,
   opAt 1321 (.Dup ⟨3, by decide⟩),
   opAt 1322 .MLOAD,
   opAt 1323 (.Swap ⟨1, by decide⟩),
   opAt 1324 (.Dup ⟨2, by decide⟩),
   opAt 1325 .ADD,
   opAt 1326 (.Swap ⟨1, by decide⟩),
   opAt 1327 (.Dup ⟨2, by decide⟩),
   opAt 1328 .LT,
   opAt 1329 .ADD,
   opAt 1330 (.Swap ⟨0, by decide⟩),
   opAt 1331 (.Dup ⟨4, by decide⟩),
   opAt 1332 .ADD,
   opAt 1333 (.Swap ⟨3, by decide⟩),
   opAt 1334 (.Dup ⟨4, by decide⟩),
   opAt 1335 .LT,
   opAt 1336 .ADD,
   opAt 1337 (.Swap ⟨2, by decide⟩),
   opAt 1338 (.Dup ⟨2, by decide⟩),
   opAt 1339 .MSTORE,
   pushAt 1340 1 31,
   opAt 1341 .NOT,
   opAt 1342 .ADD,
   opAt 1343 (.Swap ⟨0, by decide⟩),
   pushAt 1344 1 31,
   opAt 1345 .NOT,
   opAt 1346 .ADD,
   opAt 1347 (.Swap ⟨0, by decide⟩),
   opAt 1348 (.Dup ⟨5, by decide⟩),
   opAt 1349 (.Dup ⟨1, by decide⟩),
   opAt 1350 .GT,
   pushAt 1351 2 1810,
   opAt 1352 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
