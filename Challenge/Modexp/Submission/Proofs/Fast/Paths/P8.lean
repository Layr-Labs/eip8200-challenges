import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1421..1468). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1421..1468, pc 1995..2049. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1250 .JUMPDEST,
   opAt 1251 (.Dup ⟨3, by decide⟩),
   opAt 1252 (.Dup ⟨1, by decide⟩),
   opAt 1253 .MLOAD,
   opAt 1254 (.Dup ⟨1, by decide⟩),
   opAt 1255 (.Dup ⟨1, by decide⟩),
   opAt 1256 .MUL,
   opAt 1257 (.Swap ⟨1, by decide⟩),
   pushAt 1258 0 0,
   opAt 1259 .NOT,
   opAt 1260 (.Swap ⟨1, by decide⟩),
   opAt 1261 .MULMOD,
   opAt 1262 (.Dup ⟨1, by decide⟩),
   opAt 1263 (.Dup ⟨1, by decide⟩),
   opAt 1264 .LT,
   opAt 1265 (.Dup ⟨2, by decide⟩),
   opAt 1266 .ADD,
   opAt 1267 (.Swap ⟨0, by decide⟩),
   opAt 1268 .SUB,
   opAt 1269 (.Dup ⟨3, by decide⟩),
   opAt 1270 .MLOAD,
   opAt 1271 (.Swap ⟨1, by decide⟩),
   opAt 1272 (.Dup ⟨2, by decide⟩),
   opAt 1273 .ADD,
   opAt 1274 (.Swap ⟨1, by decide⟩),
   opAt 1275 (.Dup ⟨2, by decide⟩),
   opAt 1276 .LT,
   opAt 1277 .ADD,
   opAt 1278 (.Swap ⟨0, by decide⟩),
   opAt 1279 (.Dup ⟨4, by decide⟩),
   opAt 1280 .ADD,
   opAt 1281 (.Swap ⟨3, by decide⟩),
   opAt 1282 (.Dup ⟨4, by decide⟩),
   opAt 1283 .LT,
   opAt 1284 .ADD,
   opAt 1285 (.Swap ⟨2, by decide⟩),
   opAt 1286 (.Dup ⟨2, by decide⟩),
   opAt 1287 .MSTORE,
   pushAt 1288 1 31,
   opAt 1289 .NOT,
   opAt 1290 .ADD,
   opAt 1291 (.Swap ⟨0, by decide⟩),
   pushAt 1292 1 31,
   opAt 1293 .NOT,
   opAt 1294 .ADD,
   opAt 1295 (.Swap ⟨0, by decide⟩),
   opAt 1296 (.Dup ⟨5, by decide⟩),
   opAt 1297 (.Dup ⟨1, by decide⟩),
   opAt 1298 .GT,
   pushAt 1299 2 1716,
   opAt 1300 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
