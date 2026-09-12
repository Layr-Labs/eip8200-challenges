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
  [opAt 1231 .JUMPDEST,
   opAt 1232 (.Dup ⟨3, by decide⟩),
   opAt 1233 (.Dup ⟨1, by decide⟩),
   opAt 1234 .MLOAD,
   opAt 1235 (.Dup ⟨1, by decide⟩),
   opAt 1236 (.Dup ⟨1, by decide⟩),
   opAt 1237 .MUL,
   opAt 1238 (.Swap ⟨1, by decide⟩),
   pushAt 1239 0 0,
   opAt 1240 .NOT,
   opAt 1241 (.Swap ⟨1, by decide⟩),
   opAt 1242 .MULMOD,
   opAt 1243 (.Dup ⟨1, by decide⟩),
   opAt 1244 (.Dup ⟨1, by decide⟩),
   opAt 1245 .LT,
   opAt 1246 (.Dup ⟨2, by decide⟩),
   opAt 1247 .ADD,
   opAt 1248 (.Swap ⟨0, by decide⟩),
   opAt 1249 .SUB,
   opAt 1250 (.Dup ⟨3, by decide⟩),
   opAt 1251 .MLOAD,
   opAt 1252 (.Swap ⟨1, by decide⟩),
   opAt 1253 (.Dup ⟨2, by decide⟩),
   opAt 1254 .ADD,
   opAt 1255 (.Swap ⟨1, by decide⟩),
   opAt 1256 (.Dup ⟨2, by decide⟩),
   opAt 1257 .LT,
   opAt 1258 .ADD,
   opAt 1259 (.Swap ⟨0, by decide⟩),
   opAt 1260 (.Dup ⟨4, by decide⟩),
   opAt 1261 .ADD,
   opAt 1262 (.Swap ⟨3, by decide⟩),
   opAt 1263 (.Dup ⟨4, by decide⟩),
   opAt 1264 .LT,
   opAt 1265 .ADD,
   opAt 1266 (.Swap ⟨2, by decide⟩),
   opAt 1267 (.Dup ⟨2, by decide⟩),
   opAt 1268 .MSTORE,
   pushAt 1269 1 31,
   opAt 1270 .NOT,
   opAt 1271 .ADD,
   opAt 1272 (.Swap ⟨0, by decide⟩),
   pushAt 1273 1 31,
   opAt 1274 .NOT,
   opAt 1275 .ADD,
   opAt 1276 (.Swap ⟨0, by decide⟩),
   opAt 1277 (.Dup ⟨5, by decide⟩),
   opAt 1278 (.Dup ⟨1, by decide⟩),
   opAt 1279 .GT,
   pushAt 1280 2 1687,
   opAt 1281 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
