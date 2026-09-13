import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1551..1598). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1551..1598, pc 2122..2128. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1298 .JUMPDEST,
   opAt 1299 (.Dup ⟨3, by decide⟩),
   opAt 1300 (.Dup ⟨1, by decide⟩),
   opAt 1301 .MLOAD,
   opAt 1302 (.Dup ⟨1, by decide⟩),
   opAt 1303 (.Dup ⟨1, by decide⟩),
   opAt 1304 .MUL,
   opAt 1305 (.Swap ⟨1, by decide⟩),
   pushAt 1306 0 0,
   opAt 1307 .NOT,
   opAt 1308 (.Swap ⟨1, by decide⟩),
   opAt 1309 .MULMOD,
   opAt 1310 (.Dup ⟨1, by decide⟩),
   opAt 1311 (.Dup ⟨1, by decide⟩),
   opAt 1312 .LT,
   opAt 1313 (.Dup ⟨2, by decide⟩),
   opAt 1314 .ADD,
   opAt 1315 (.Swap ⟨0, by decide⟩),
   opAt 1316 .SUB,
   opAt 1317 (.Dup ⟨3, by decide⟩),
   opAt 1318 .MLOAD,
   opAt 1319 (.Swap ⟨1, by decide⟩),
   opAt 1320 (.Dup ⟨2, by decide⟩),
   opAt 1321 .ADD,
   opAt 1322 (.Swap ⟨1, by decide⟩),
   opAt 1323 (.Dup ⟨2, by decide⟩),
   opAt 1324 .LT,
   opAt 1325 .ADD,
   opAt 1326 (.Swap ⟨0, by decide⟩),
   opAt 1327 (.Dup ⟨4, by decide⟩),
   opAt 1328 .ADD,
   opAt 1329 (.Swap ⟨3, by decide⟩),
   opAt 1330 (.Dup ⟨4, by decide⟩),
   opAt 1331 .LT,
   opAt 1332 .ADD,
   opAt 1333 (.Swap ⟨2, by decide⟩),
   opAt 1334 (.Dup ⟨2, by decide⟩),
   opAt 1335 .MSTORE,
   pushAt 1336 1 31,
   opAt 1337 .NOT,
   opAt 1338 .ADD,
   opAt 1339 (.Swap ⟨0, by decide⟩),
   pushAt 1340 1 31,
   opAt 1341 .NOT,
   opAt 1342 .ADD,
   opAt 1343 (.Swap ⟨0, by decide⟩),
   opAt 1344 (.Dup ⟨5, by decide⟩),
   opAt 1345 (.Dup ⟨1, by decide⟩),
   opAt 1346 .GT,
   pushAt 1347 2 1802,
   opAt 1348 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
