import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1369..1420). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1369..1375, pc 1926..1935. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1255 .JUMPDEST,
   pushAt 1256 1 1,
   opAt 1257 (.Swap ⟨0, by decide⟩),
   opAt 1258 .SUB,
   opAt 1259 (.Dup ⟨0, by decide⟩),
   pushAt 1260 2 1737,
   opAt 1261 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1262 .POP,
   opAt 1263 .POP,
   opAt 1264 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1265 .JUMPDEST,
   pushAt 1266 2 5248,
   opAt 1267 .MLOAD,
   opAt 1268 (.Dup ⟨0, by decide⟩),
   pushAt 1269 1 64,
   opAt 1270 .ADD,
   opAt 1271 .CALLDATASIZE,
   pushAt 1272 2 4096,
   opAt 1273 .CALLDATACOPY,
   opAt 1274 (.Dup ⟨0, by decide⟩),
   opAt 1275 (.Dup ⟨3, by decide⟩),
   opAt 1276 .ADD,
   pushAt 1277 1 32,
   opAt 1278 (.Swap ⟨0, by decide⟩),
   opAt 1279 .SUB,
   pushAt 1280 1 32,
   opAt 1281 (.Dup ⟨4, by decide⟩),
   opAt 1282 .SUB,
   opAt 1283 (.Swap ⟨3, by decide⟩),
   opAt 1284 .POP,
   opAt 1285 (.Swap ⟨0, by decide⟩),
   opAt 1286 .POP,
   pushAt 1287 1 32,
   opAt 1288 (.Dup ⟨2, by decide⟩),
   opAt 1289 .SUB,
   opAt 1290 (.Swap ⟨1, by decide⟩),
   opAt 1291 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1292 .JUMPDEST,
   opAt 1293 (.Dup ⟨0, by decide⟩),
   opAt 1294 .MLOAD,
   pushAt 1295 0 0,
   pushAt 1296 2 5344,
   opAt 1297 .MLOAD,
   opAt 1298 (.Dup ⟨4, by decide⟩),
   pushAt 1299 2 5248,
   opAt 1300 .MLOAD,
   opAt 1301 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
