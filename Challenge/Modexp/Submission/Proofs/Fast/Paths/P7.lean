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
  [opAt 1247 .JUMPDEST,
   pushAt 1248 1 1,
   opAt 1249 (.Swap ⟨0, by decide⟩),
   opAt 1250 .SUB,
   opAt 1251 (.Dup ⟨0, by decide⟩),
   pushAt 1252 2 1729,
   opAt 1253 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2065. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1254 .POP,
   opAt 1255 .POP,
   opAt 1256 .JUMP]

/-- Instructions 1509..1487, pc 2066..2100. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1257 .JUMPDEST,
   pushAt 1258 2 2688,
   opAt 1259 .MLOAD,
   opAt 1260 (.Dup ⟨0, by decide⟩),
   pushAt 1261 1 64,
   opAt 1262 .ADD,
   opAt 1263 .CALLDATASIZE,
   pushAt 1264 2 2048,
   opAt 1265 .CALLDATACOPY,
   opAt 1266 (.Dup ⟨0, by decide⟩),
   opAt 1267 (.Dup ⟨3, by decide⟩),
   opAt 1268 .ADD,
   pushAt 1269 1 32,
   opAt 1270 (.Swap ⟨0, by decide⟩),
   opAt 1271 .SUB,
   pushAt 1272 1 32,
   opAt 1273 (.Dup ⟨4, by decide⟩),
   opAt 1274 .SUB,
   opAt 1275 (.Swap ⟨3, by decide⟩),
   opAt 1276 .POP,
   opAt 1277 (.Swap ⟨0, by decide⟩),
   opAt 1278 .POP,
   pushAt 1279 1 32,
   opAt 1280 (.Dup ⟨2, by decide⟩),
   opAt 1281 .SUB,
   opAt 1282 (.Swap ⟨1, by decide⟩),
   opAt 1283 .POP]

/-- Instructions 1536..1550, pc 2101..2121. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1284 .JUMPDEST,
   opAt 1285 (.Dup ⟨0, by decide⟩),
   opAt 1286 .MLOAD,
   pushAt 1287 0 0,
   pushAt 1288 2 2784,
   opAt 1289 .MLOAD,
   opAt 1290 (.Dup ⟨4, by decide⟩),
   pushAt 1291 2 2688,
   opAt 1292 .MLOAD,
   opAt 1293 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
