import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1551..1598). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1551..1598, pc 2125..2131. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1299 .JUMPDEST,
   opAt 1300 (.Dup ⟨3, by decide⟩),
   opAt 1301 (.Dup ⟨1, by decide⟩),
   opAt 1302 .MLOAD,
   opAt 1303 (.Dup ⟨1, by decide⟩),
   opAt 1304 (.Dup ⟨1, by decide⟩),
   opAt 1305 .MUL,
   opAt 1306 (.Swap ⟨1, by decide⟩),
   pushAt 1307 0 0,
   opAt 1308 .NOT,
   opAt 1309 (.Swap ⟨1, by decide⟩),
   opAt 1310 .MULMOD,
   opAt 1311 (.Dup ⟨1, by decide⟩),
   opAt 1312 (.Dup ⟨1, by decide⟩),
   opAt 1313 .LT,
   opAt 1314 (.Dup ⟨2, by decide⟩),
   opAt 1315 .ADD,
   opAt 1316 (.Swap ⟨0, by decide⟩),
   opAt 1317 .SUB,
   opAt 1318 (.Dup ⟨3, by decide⟩),
   opAt 1319 .MLOAD,
   opAt 1320 (.Swap ⟨1, by decide⟩),
   opAt 1321 (.Dup ⟨2, by decide⟩),
   opAt 1322 .ADD,
   opAt 1323 (.Swap ⟨1, by decide⟩),
   opAt 1324 (.Dup ⟨2, by decide⟩),
   opAt 1325 .LT,
   opAt 1326 .ADD,
   opAt 1327 (.Swap ⟨0, by decide⟩),
   opAt 1328 (.Dup ⟨4, by decide⟩),
   opAt 1329 .ADD,
   opAt 1330 (.Swap ⟨3, by decide⟩),
   opAt 1331 (.Dup ⟨4, by decide⟩),
   opAt 1332 .LT,
   opAt 1333 .ADD,
   opAt 1334 (.Swap ⟨2, by decide⟩),
   opAt 1335 (.Dup ⟨2, by decide⟩),
   opAt 1336 .MSTORE,
   pushAt 1337 1 31,
   opAt 1338 .NOT,
   opAt 1339 .ADD,
   opAt 1340 (.Swap ⟨0, by decide⟩),
   pushAt 1341 1 31,
   opAt 1342 .NOT,
   opAt 1343 .ADD,
   opAt 1344 (.Swap ⟨0, by decide⟩),
   opAt 1345 (.Dup ⟨5, by decide⟩),
   opAt 1346 (.Dup ⟨1, by decide⟩),
   opAt 1347 .GT,
   pushAt 1348 2 1805,
   opAt 1349 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
