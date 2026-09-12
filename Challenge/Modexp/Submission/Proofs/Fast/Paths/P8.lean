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
  [opAt 1226 .JUMPDEST,
   opAt 1227 (.Dup ⟨3, by decide⟩),
   opAt 1228 (.Dup ⟨1, by decide⟩),
   opAt 1229 .MLOAD,
   opAt 1230 (.Dup ⟨1, by decide⟩),
   opAt 1231 (.Dup ⟨1, by decide⟩),
   opAt 1232 .MUL,
   opAt 1233 (.Swap ⟨1, by decide⟩),
   pushAt 1234 0 0,
   opAt 1235 .NOT,
   opAt 1236 (.Swap ⟨1, by decide⟩),
   opAt 1237 .MULMOD,
   opAt 1238 (.Dup ⟨1, by decide⟩),
   opAt 1239 (.Dup ⟨1, by decide⟩),
   opAt 1240 .LT,
   opAt 1241 (.Dup ⟨2, by decide⟩),
   opAt 1242 .ADD,
   opAt 1243 (.Swap ⟨0, by decide⟩),
   opAt 1244 .SUB,
   opAt 1245 (.Dup ⟨3, by decide⟩),
   opAt 1246 .MLOAD,
   opAt 1247 (.Swap ⟨1, by decide⟩),
   opAt 1248 (.Dup ⟨2, by decide⟩),
   opAt 1249 .ADD,
   opAt 1250 (.Swap ⟨1, by decide⟩),
   opAt 1251 (.Dup ⟨2, by decide⟩),
   opAt 1252 .LT,
   opAt 1253 .ADD,
   opAt 1254 (.Swap ⟨0, by decide⟩),
   opAt 1255 (.Dup ⟨4, by decide⟩),
   opAt 1256 .ADD,
   opAt 1257 (.Swap ⟨3, by decide⟩),
   opAt 1258 (.Dup ⟨4, by decide⟩),
   opAt 1259 .LT,
   opAt 1260 .ADD,
   opAt 1261 (.Swap ⟨2, by decide⟩),
   opAt 1262 (.Dup ⟨2, by decide⟩),
   opAt 1263 .MSTORE,
   pushAt 1264 1 31,
   opAt 1265 .NOT,
   opAt 1266 .ADD,
   opAt 1267 (.Swap ⟨0, by decide⟩),
   pushAt 1268 1 31,
   opAt 1269 .NOT,
   opAt 1270 .ADD,
   opAt 1271 (.Swap ⟨0, by decide⟩),
   opAt 1272 (.Dup ⟨5, by decide⟩),
   opAt 1273 (.Dup ⟨1, by decide⟩),
   opAt 1274 .GT,
   pushAt 1275 2 1675,
   opAt 1276 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
