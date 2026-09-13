import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1551..1598). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1551..1598, pc 2120..2126. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1296 .JUMPDEST,
   opAt 1297 (.Dup ⟨3, by decide⟩),
   opAt 1298 (.Dup ⟨1, by decide⟩),
   opAt 1299 .MLOAD,
   opAt 1300 (.Dup ⟨1, by decide⟩),
   opAt 1301 (.Dup ⟨1, by decide⟩),
   opAt 1302 .MUL,
   opAt 1303 (.Swap ⟨1, by decide⟩),
   pushAt 1304 0 0,
   opAt 1305 .NOT,
   opAt 1306 (.Swap ⟨1, by decide⟩),
   opAt 1307 .MULMOD,
   opAt 1308 (.Dup ⟨1, by decide⟩),
   opAt 1309 (.Dup ⟨1, by decide⟩),
   opAt 1310 .LT,
   opAt 1311 (.Dup ⟨2, by decide⟩),
   opAt 1312 .ADD,
   opAt 1313 (.Swap ⟨0, by decide⟩),
   opAt 1314 .SUB,
   opAt 1315 (.Dup ⟨3, by decide⟩),
   opAt 1316 .MLOAD,
   opAt 1317 (.Swap ⟨1, by decide⟩),
   opAt 1318 (.Dup ⟨2, by decide⟩),
   opAt 1319 .ADD,
   opAt 1320 (.Swap ⟨1, by decide⟩),
   opAt 1321 (.Dup ⟨2, by decide⟩),
   opAt 1322 .LT,
   opAt 1323 .ADD,
   opAt 1324 (.Swap ⟨0, by decide⟩),
   opAt 1325 (.Dup ⟨4, by decide⟩),
   opAt 1326 .ADD,
   opAt 1327 (.Swap ⟨3, by decide⟩),
   opAt 1328 (.Dup ⟨4, by decide⟩),
   opAt 1329 .LT,
   opAt 1330 .ADD,
   opAt 1331 (.Swap ⟨2, by decide⟩),
   opAt 1332 (.Dup ⟨2, by decide⟩),
   opAt 1333 .MSTORE,
   pushAt 1334 1 31,
   opAt 1335 .NOT,
   opAt 1336 .ADD,
   opAt 1337 (.Swap ⟨0, by decide⟩),
   pushAt 1338 1 31,
   opAt 1339 .NOT,
   opAt 1340 .ADD,
   opAt 1341 (.Swap ⟨0, by decide⟩),
   opAt 1342 (.Dup ⟨5, by decide⟩),
   opAt 1343 (.Dup ⟨1, by decide⟩),
   opAt 1344 .GT,
   pushAt 1345 2 1800,
   opAt 1346 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
