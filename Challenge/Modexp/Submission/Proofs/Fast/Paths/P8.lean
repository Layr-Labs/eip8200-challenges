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
  [opAt 1293 .JUMPDEST,
   opAt 1294 (.Dup ⟨3, by decide⟩),
   opAt 1295 (.Dup ⟨1, by decide⟩),
   opAt 1296 .MLOAD,
   opAt 1297 (.Dup ⟨1, by decide⟩),
   opAt 1298 (.Dup ⟨1, by decide⟩),
   opAt 1299 .MUL,
   opAt 1300 (.Swap ⟨1, by decide⟩),
   pushAt 1301 0 0,
   opAt 1302 .NOT,
   opAt 1303 (.Swap ⟨1, by decide⟩),
   opAt 1304 .MULMOD,
   opAt 1305 (.Dup ⟨1, by decide⟩),
   opAt 1306 (.Dup ⟨1, by decide⟩),
   opAt 1307 .LT,
   opAt 1308 (.Dup ⟨2, by decide⟩),
   opAt 1309 .ADD,
   opAt 1310 (.Swap ⟨0, by decide⟩),
   opAt 1311 .SUB,
   opAt 1312 (.Dup ⟨3, by decide⟩),
   opAt 1313 .MLOAD,
   opAt 1314 (.Swap ⟨1, by decide⟩),
   opAt 1315 (.Dup ⟨2, by decide⟩),
   opAt 1316 .ADD,
   opAt 1317 (.Swap ⟨1, by decide⟩),
   opAt 1318 (.Dup ⟨2, by decide⟩),
   opAt 1319 .LT,
   opAt 1320 .ADD,
   opAt 1321 (.Swap ⟨0, by decide⟩),
   opAt 1322 (.Dup ⟨4, by decide⟩),
   opAt 1323 .ADD,
   opAt 1324 (.Swap ⟨3, by decide⟩),
   opAt 1325 (.Dup ⟨4, by decide⟩),
   opAt 1326 .LT,
   opAt 1327 .ADD,
   opAt 1328 (.Swap ⟨2, by decide⟩),
   opAt 1329 (.Dup ⟨2, by decide⟩),
   opAt 1330 .MSTORE,
   pushAt 1331 1 31,
   opAt 1332 .NOT,
   opAt 1333 .ADD,
   opAt 1334 (.Swap ⟨0, by decide⟩),
   pushAt 1335 1 31,
   opAt 1336 .NOT,
   opAt 1337 .ADD,
   opAt 1338 (.Swap ⟨0, by decide⟩),
   opAt 1339 (.Dup ⟨5, by decide⟩),
   opAt 1340 (.Dup ⟨1, by decide⟩),
   opAt 1341 .GT,
   pushAt 1342 2 1802,
   opAt 1343 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
