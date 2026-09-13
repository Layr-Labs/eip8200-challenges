import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1451..1550). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1451..1505, pc 2051..2060. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1249 .JUMPDEST,
   pushAt 1250 1 1,
   opAt 1251 (.Swap ⟨0, by decide⟩),
   opAt 1252 .SUB,
   opAt 1253 (.Dup ⟨0, by decide⟩),
   pushAt 1254 2 1727,
   opAt 1255 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2063. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1256 .POP,
   opAt 1257 .POP,
   opAt 1258 .JUMP]

/-- Instructions 1509..1487, pc 2064..2098. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1259 .JUMPDEST,
   pushAt 1260 2 2688,
   opAt 1261 .MLOAD,
   opAt 1262 (.Dup ⟨0, by decide⟩),
   pushAt 1263 1 64,
   opAt 1264 .ADD,
   opAt 1265 .CALLDATASIZE,
   pushAt 1266 2 2048,
   opAt 1267 .CALLDATACOPY,
   opAt 1268 (.Dup ⟨0, by decide⟩),
   opAt 1269 (.Dup ⟨3, by decide⟩),
   opAt 1270 .ADD,
   pushAt 1271 1 32,
   opAt 1272 (.Swap ⟨0, by decide⟩),
   opAt 1273 .SUB,
   pushAt 1274 1 32,
   opAt 1275 (.Dup ⟨4, by decide⟩),
   opAt 1276 .SUB,
   opAt 1277 (.Swap ⟨3, by decide⟩),
   opAt 1278 .POP,
   opAt 1279 (.Swap ⟨0, by decide⟩),
   opAt 1280 .POP,
   pushAt 1281 1 32,
   opAt 1282 (.Dup ⟨2, by decide⟩),
   opAt 1283 .SUB,
   opAt 1284 (.Swap ⟨1, by decide⟩),
   opAt 1285 .POP]

/-- Instructions 1536..1550, pc 2099..2119. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1286 .JUMPDEST,
   opAt 1287 (.Dup ⟨0, by decide⟩),
   opAt 1288 .MLOAD,
   pushAt 1289 0 0,
   pushAt 1290 2 2784,
   opAt 1291 .MLOAD,
   opAt 1292 (.Dup ⟨4, by decide⟩),
   pushAt 1293 2 2688,
   opAt 1294 .MLOAD,
   opAt 1295 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
