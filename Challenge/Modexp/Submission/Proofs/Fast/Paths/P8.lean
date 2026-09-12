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
  [opAt 1301 .JUMPDEST,
   opAt 1302 (.Dup ⟨3, by decide⟩),
   opAt 1303 (.Dup ⟨1, by decide⟩),
   opAt 1304 .MLOAD,
   opAt 1305 (.Dup ⟨1, by decide⟩),
   opAt 1306 (.Dup ⟨1, by decide⟩),
   opAt 1307 .MUL,
   opAt 1308 (.Swap ⟨1, by decide⟩),
   pushAt 1309 0 0,
   opAt 1310 .NOT,
   opAt 1311 (.Swap ⟨1, by decide⟩),
   opAt 1312 .MULMOD,
   opAt 1313 (.Dup ⟨1, by decide⟩),
   opAt 1314 (.Dup ⟨1, by decide⟩),
   opAt 1315 .LT,
   opAt 1316 (.Dup ⟨2, by decide⟩),
   opAt 1317 .ADD,
   opAt 1318 (.Swap ⟨0, by decide⟩),
   opAt 1319 .SUB,
   opAt 1320 (.Dup ⟨3, by decide⟩),
   opAt 1321 .MLOAD,
   opAt 1322 (.Swap ⟨1, by decide⟩),
   opAt 1323 (.Dup ⟨2, by decide⟩),
   opAt 1324 .ADD,
   opAt 1325 (.Swap ⟨1, by decide⟩),
   opAt 1326 (.Dup ⟨2, by decide⟩),
   opAt 1327 .LT,
   opAt 1328 .ADD,
   opAt 1329 (.Swap ⟨0, by decide⟩),
   opAt 1330 (.Dup ⟨4, by decide⟩),
   opAt 1331 .ADD,
   opAt 1332 (.Swap ⟨3, by decide⟩),
   opAt 1333 (.Dup ⟨4, by decide⟩),
   opAt 1334 .LT,
   opAt 1335 .ADD,
   opAt 1336 (.Swap ⟨2, by decide⟩),
   opAt 1337 (.Dup ⟨2, by decide⟩),
   opAt 1338 .MSTORE,
   pushAt 1339 1 31,
   opAt 1340 .NOT,
   opAt 1341 .ADD,
   opAt 1342 (.Swap ⟨0, by decide⟩),
   pushAt 1343 1 31,
   opAt 1344 .NOT,
   opAt 1345 .ADD,
   opAt 1346 (.Swap ⟨0, by decide⟩),
   opAt 1347 (.Dup ⟨5, by decide⟩),
   opAt 1348 (.Dup ⟨1, by decide⟩),
   opAt 1349 .GT,
   pushAt 1350 2 1810,
   opAt 1351 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
