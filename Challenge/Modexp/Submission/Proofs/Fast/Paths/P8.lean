import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1469..1516). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1469..1516, pc 2043..2049. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1261 .JUMPDEST,
   opAt 1262 (.Dup ⟨3, by decide⟩),
   opAt 1263 (.Dup ⟨1, by decide⟩),
   opAt 1264 .MLOAD,
   opAt 1265 (.Dup ⟨1, by decide⟩),
   opAt 1266 (.Dup ⟨1, by decide⟩),
   opAt 1267 .MUL,
   opAt 1268 (.Swap ⟨1, by decide⟩),
   pushAt 1269 0 0,
   opAt 1270 .NOT,
   opAt 1271 (.Swap ⟨1, by decide⟩),
   opAt 1272 .MULMOD,
   opAt 1273 (.Dup ⟨1, by decide⟩),
   opAt 1274 (.Dup ⟨1, by decide⟩),
   opAt 1275 .LT,
   opAt 1276 (.Dup ⟨2, by decide⟩),
   opAt 1277 .ADD,
   opAt 1278 (.Swap ⟨0, by decide⟩),
   opAt 1279 .SUB,
   opAt 1280 (.Dup ⟨3, by decide⟩),
   opAt 1281 .MLOAD,
   opAt 1282 (.Swap ⟨1, by decide⟩),
   opAt 1283 (.Dup ⟨2, by decide⟩),
   opAt 1284 .ADD,
   opAt 1285 (.Swap ⟨1, by decide⟩),
   opAt 1286 (.Dup ⟨2, by decide⟩),
   opAt 1287 .LT,
   opAt 1288 .ADD,
   opAt 1289 (.Swap ⟨0, by decide⟩),
   opAt 1290 (.Dup ⟨4, by decide⟩),
   opAt 1291 .ADD,
   opAt 1292 (.Swap ⟨3, by decide⟩),
   opAt 1293 (.Dup ⟨4, by decide⟩),
   opAt 1294 .LT,
   opAt 1295 .ADD,
   opAt 1296 (.Swap ⟨2, by decide⟩),
   opAt 1297 (.Dup ⟨2, by decide⟩),
   opAt 1298 .MSTORE,
   pushAt 1299 1 31,
   opAt 1300 .NOT,
   opAt 1301 .ADD,
   opAt 1302 (.Swap ⟨0, by decide⟩),
   pushAt 1303 1 31,
   opAt 1304 .NOT,
   opAt 1305 .ADD,
   opAt 1306 (.Swap ⟨0, by decide⟩),
   opAt 1307 (.Dup ⟨5, by decide⟩),
   opAt 1308 (.Dup ⟨1, by decide⟩),
   opAt 1309 .GT,
   pushAt 1310 2 1723,
   opAt 1311 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
