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
  [opAt 1294 .JUMPDEST,
   opAt 1295 (.Dup ⟨3, by decide⟩),
   opAt 1296 (.Dup ⟨1, by decide⟩),
   opAt 1297 .MLOAD,
   opAt 1298 (.Dup ⟨1, by decide⟩),
   opAt 1299 (.Dup ⟨1, by decide⟩),
   opAt 1300 .MUL,
   opAt 1301 (.Swap ⟨1, by decide⟩),
   pushAt 1302 0 0,
   opAt 1303 .NOT,
   opAt 1304 (.Swap ⟨1, by decide⟩),
   opAt 1305 .MULMOD,
   opAt 1306 (.Dup ⟨1, by decide⟩),
   opAt 1307 (.Dup ⟨1, by decide⟩),
   opAt 1308 .LT,
   opAt 1309 (.Dup ⟨2, by decide⟩),
   opAt 1310 .ADD,
   opAt 1311 (.Swap ⟨0, by decide⟩),
   opAt 1312 .SUB,
   opAt 1313 (.Dup ⟨3, by decide⟩),
   opAt 1314 .MLOAD,
   opAt 1315 (.Swap ⟨1, by decide⟩),
   opAt 1316 (.Dup ⟨2, by decide⟩),
   opAt 1317 .ADD,
   opAt 1318 (.Swap ⟨1, by decide⟩),
   opAt 1319 (.Dup ⟨2, by decide⟩),
   opAt 1320 .LT,
   opAt 1321 .ADD,
   opAt 1322 (.Swap ⟨0, by decide⟩),
   opAt 1323 (.Dup ⟨4, by decide⟩),
   opAt 1324 .ADD,
   opAt 1325 (.Swap ⟨3, by decide⟩),
   opAt 1326 (.Dup ⟨4, by decide⟩),
   opAt 1327 .LT,
   opAt 1328 .ADD,
   opAt 1329 (.Swap ⟨2, by decide⟩),
   opAt 1330 (.Dup ⟨2, by decide⟩),
   opAt 1331 .MSTORE,
   pushAt 1332 1 31,
   opAt 1333 .NOT,
   opAt 1334 .ADD,
   opAt 1335 (.Swap ⟨0, by decide⟩),
   pushAt 1336 1 31,
   opAt 1337 .NOT,
   opAt 1338 .ADD,
   opAt 1339 (.Swap ⟨0, by decide⟩),
   opAt 1340 (.Dup ⟨5, by decide⟩),
   opAt 1341 (.Dup ⟨1, by decide⟩),
   opAt 1342 .GT,
   pushAt 1343 2 1802,
   opAt 1344 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
