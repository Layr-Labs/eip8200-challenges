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
  [opAt 1224 .JUMPDEST,
   opAt 1225 (.Dup ⟨3, by decide⟩),
   opAt 1226 (.Dup ⟨1, by decide⟩),
   opAt 1227 .MLOAD,
   opAt 1228 (.Dup ⟨1, by decide⟩),
   opAt 1229 (.Dup ⟨1, by decide⟩),
   opAt 1230 .MUL,
   opAt 1231 (.Swap ⟨1, by decide⟩),
   pushAt 1232 0 0,
   opAt 1233 .NOT,
   opAt 1234 (.Swap ⟨1, by decide⟩),
   opAt 1235 .MULMOD,
   opAt 1236 (.Dup ⟨1, by decide⟩),
   opAt 1237 (.Dup ⟨1, by decide⟩),
   opAt 1238 .LT,
   opAt 1239 (.Dup ⟨2, by decide⟩),
   opAt 1240 .ADD,
   opAt 1241 (.Swap ⟨0, by decide⟩),
   opAt 1242 .SUB,
   opAt 1243 (.Dup ⟨3, by decide⟩),
   opAt 1244 .MLOAD,
   opAt 1245 (.Swap ⟨1, by decide⟩),
   opAt 1246 (.Dup ⟨2, by decide⟩),
   opAt 1247 .ADD,
   opAt 1248 (.Swap ⟨1, by decide⟩),
   opAt 1249 (.Dup ⟨2, by decide⟩),
   opAt 1250 .LT,
   opAt 1251 .ADD,
   opAt 1252 (.Swap ⟨0, by decide⟩),
   opAt 1253 (.Dup ⟨4, by decide⟩),
   opAt 1254 .ADD,
   opAt 1255 (.Swap ⟨3, by decide⟩),
   opAt 1256 (.Dup ⟨4, by decide⟩),
   opAt 1257 .LT,
   opAt 1258 .ADD,
   opAt 1259 (.Swap ⟨2, by decide⟩),
   opAt 1260 (.Dup ⟨2, by decide⟩),
   opAt 1261 .MSTORE,
   pushAt 1262 1 31,
   opAt 1263 .NOT,
   opAt 1264 .ADD,
   opAt 1265 (.Swap ⟨0, by decide⟩),
   pushAt 1266 1 31,
   opAt 1267 .NOT,
   opAt 1268 .ADD,
   opAt 1269 (.Swap ⟨0, by decide⟩),
   opAt 1270 (.Dup ⟨5, by decide⟩),
   opAt 1271 (.Dup ⟨1, by decide⟩),
   opAt 1272 .GT,
   pushAt 1273 2 1671,
   opAt 1274 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
