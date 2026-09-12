import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1519..1568). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1519..1568, pc 2119..2178. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1224 .JUMPDEST,
   opAt 1225 (.Dup ⟨0, by decide⟩),
   opAt 1226 .MLOAD,
   pushAt 1227 0 0,
   opAt 1228 .NOT,
   opAt 1229 (.Dup ⟨5, by decide⟩),
   opAt 1230 (.Dup ⟨2, by decide⟩),
   opAt 1231 .MUL,
   opAt 1232 (.Swap ⟨1, by decide⟩),
   opAt 1233 (.Dup ⟨6, by decide⟩),
   opAt 1234 .MULMOD,
   opAt 1235 (.Dup ⟨1, by decide⟩),
   opAt 1236 (.Dup ⟨1, by decide⟩),
   opAt 1237 .LT,
   opAt 1238 .SUB,
   opAt 1239 (.Dup ⟨4, by decide⟩),
   opAt 1240 (.Dup ⟨2, by decide⟩),
   opAt 1241 .ADD,
   opAt 1242 (.Dup ⟨0, by decide⟩),
   opAt 1243 (.Swap ⟨5, by decide⟩),
   opAt 1244 .GT,
   opAt 1245 .SUB,
   opAt 1246 .SUB,
   opAt 1247 (.Dup ⟨3, by decide⟩),
   opAt 1248 (.Dup ⟨3, by decide⟩),
   opAt 1249 .MLOAD,
   opAt 1250 .ADD,
   opAt 1251 (.Dup ⟨0, by decide⟩),
   opAt 1252 (.Swap ⟨4, by decide⟩),
   opAt 1253 .GT,
   opAt 1254 .ADD,
   opAt 1255 (.Swap ⟨2, by decide⟩),
   pushAt 1256 1 32,
   opAt 1257 (.Dup ⟨3, by decide⟩),
   pushAt 1258 1 31,
   opAt 1259 .NOT,
   opAt 1260 .ADD,
   opAt 1261 (.Swap ⟨3, by decide⟩),
   opAt 1262 .ADD,
   opAt 1263 .MSTORE,
   pushAt 1264 1 31,
   opAt 1265 .NOT,
   opAt 1266 .ADD,
   pushAt 1267 2 8224,
   opAt 1268 (.Dup ⟨2, by decide⟩),
   opAt 1269 .GT,
   pushAt 1270 2 1666,
   opAt 1271 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
