import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1469..1518). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1469..1518, pc 2050..2118. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1301 .POP,
   opAt 1302 .POP,
   opAt 1303 (.Dup ⟨0, by decide⟩),
   pushAt 1304 2 2080,
   opAt 1305 .MLOAD,
   opAt 1306 .ADD,
   opAt 1307 (.Dup ⟨0, by decide⟩),
   pushAt 1308 2 2080,
   opAt 1309 .MSTORE,
   opAt 1310 .LT,
   pushAt 1311 2 2048,
   opAt 1312 .MSTORE,
   pushAt 1313 2 2880,
   opAt 1314 .MLOAD,
   opAt 1315 .MLOAD,
   pushAt 1316 2 2816,
   opAt 1317 .MLOAD,
   opAt 1318 .MUL,
   opAt 1319 (.Dup ⟨0, by decide⟩),
   pushAt 1320 2 2848,
   opAt 1321 .MLOAD,
   opAt 1322 .MLOAD,
   opAt 1323 (.Dup ⟨1, by decide⟩),
   opAt 1324 (.Dup ⟨1, by decide⟩),
   opAt 1325 .MUL,
   opAt 1326 (.Swap ⟨1, by decide⟩),
   pushAt 1327 0 0,
   opAt 1328 .NOT,
   opAt 1329 (.Swap ⟨1, by decide⟩),
   opAt 1330 .MULMOD,
   opAt 1331 (.Dup ⟨1, by decide⟩),
   opAt 1332 (.Dup ⟨1, by decide⟩),
   opAt 1333 .LT,
   opAt 1334 (.Dup ⟨2, by decide⟩),
   opAt 1335 .ADD,
   opAt 1336 (.Swap ⟨0, by decide⟩),
   opAt 1337 .SUB,
   opAt 1338 (.Swap ⟨0, by decide⟩),
   pushAt 1339 0 0,
   opAt 1340 .LT,
   opAt 1341 .ADD,
   pushAt 1342 2 2880,
   opAt 1343 .MLOAD,
   pushAt 1344 1 32,
   opAt 1345 (.Swap ⟨0, by decide⟩),
   opAt 1346 .SUB,
   pushAt 1347 2 2848,
   opAt 1348 .MLOAD,
   pushAt 1349 1 32,
   opAt 1350 (.Swap ⟨0, by decide⟩),
   opAt 1351 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
