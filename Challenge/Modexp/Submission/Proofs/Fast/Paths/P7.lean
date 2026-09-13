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
  [opAt 1246 .JUMPDEST,
   pushAt 1247 1 1,
   opAt 1248 (.Swap ⟨0, by decide⟩),
   opAt 1249 .SUB,
   opAt 1250 (.Dup ⟨0, by decide⟩),
   pushAt 1251 2 1729,
   opAt 1252 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2065. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1253 .POP,
   opAt 1254 .POP,
   opAt 1255 .JUMP]

/-- Instructions 1509..1487, pc 2066..2100. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1256 .JUMPDEST,
   pushAt 1257 2 2688,
   opAt 1258 .MLOAD,
   opAt 1259 (.Dup ⟨0, by decide⟩),
   pushAt 1260 1 64,
   opAt 1261 .ADD,
   opAt 1262 .CALLDATASIZE,
   pushAt 1263 2 2048,
   opAt 1264 .CALLDATACOPY,
   opAt 1265 (.Dup ⟨0, by decide⟩),
   opAt 1266 (.Dup ⟨3, by decide⟩),
   opAt 1267 .ADD,
   pushAt 1268 1 32,
   opAt 1269 (.Swap ⟨0, by decide⟩),
   opAt 1270 .SUB,
   pushAt 1271 1 32,
   opAt 1272 (.Dup ⟨4, by decide⟩),
   opAt 1273 .SUB,
   opAt 1274 (.Swap ⟨3, by decide⟩),
   opAt 1275 .POP,
   opAt 1276 (.Swap ⟨0, by decide⟩),
   opAt 1277 .POP,
   pushAt 1278 1 32,
   opAt 1279 (.Dup ⟨2, by decide⟩),
   opAt 1280 .SUB,
   opAt 1281 (.Swap ⟨1, by decide⟩),
   opAt 1282 .POP]

/-- Instructions 1536..1550, pc 2101..2121. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1283 .JUMPDEST,
   opAt 1284 (.Dup ⟨0, by decide⟩),
   opAt 1285 .MLOAD,
   pushAt 1286 0 0,
   pushAt 1287 2 2784,
   opAt 1288 .MLOAD,
   opAt 1289 (.Dup ⟨4, by decide⟩),
   pushAt 1290 2 2688,
   opAt 1291 .MLOAD,
   opAt 1292 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
