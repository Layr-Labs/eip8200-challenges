import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1451..1550). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1451..1505, pc 2053..2062. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1251 .JUMPDEST,
   pushAt 1252 1 1,
   opAt 1253 (.Swap ⟨0, by decide⟩),
   opAt 1254 .SUB,
   opAt 1255 (.Dup ⟨0, by decide⟩),
   pushAt 1256 2 1729,
   opAt 1257 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2065. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1258 .POP,
   opAt 1259 .POP,
   opAt 1260 .JUMP]

/-- Instructions 1509..1487, pc 2066..2100. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1261 .JUMPDEST,
   pushAt 1262 2 2688,
   opAt 1263 .MLOAD,
   opAt 1264 (.Dup ⟨0, by decide⟩),
   pushAt 1265 1 64,
   opAt 1266 .ADD,
   opAt 1267 .CALLDATASIZE,
   pushAt 1268 2 2048,
   opAt 1269 .CALLDATACOPY,
   opAt 1270 (.Dup ⟨0, by decide⟩),
   opAt 1271 (.Dup ⟨3, by decide⟩),
   opAt 1272 .ADD,
   pushAt 1273 1 32,
   opAt 1274 (.Swap ⟨0, by decide⟩),
   opAt 1275 .SUB,
   pushAt 1276 1 32,
   opAt 1277 (.Dup ⟨4, by decide⟩),
   opAt 1278 .SUB,
   opAt 1279 (.Swap ⟨3, by decide⟩),
   opAt 1280 .POP,
   opAt 1281 (.Swap ⟨0, by decide⟩),
   opAt 1282 .POP,
   pushAt 1283 1 32,
   opAt 1284 (.Dup ⟨2, by decide⟩),
   opAt 1285 .SUB,
   opAt 1286 (.Swap ⟨1, by decide⟩),
   opAt 1287 .POP]

/-- Instructions 1536..1550, pc 2101..2121. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1288 .JUMPDEST,
   opAt 1289 (.Dup ⟨0, by decide⟩),
   opAt 1290 .MLOAD,
   pushAt 1291 0 0,
   pushAt 1292 2 2784,
   opAt 1293 .MLOAD,
   opAt 1294 (.Dup ⟨4, by decide⟩),
   pushAt 1295 2 2688,
   opAt 1296 .MLOAD,
   opAt 1297 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
