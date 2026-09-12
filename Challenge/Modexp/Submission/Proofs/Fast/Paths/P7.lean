import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1369..1468). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1369..1423, pc 1974..1983. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1214 .JUMPDEST,
   pushAt 1215 1 1,
   opAt 1216 (.Swap ⟨0, by decide⟩),
   opAt 1217 .SUB,
   opAt 1218 (.Dup ⟨0, by decide⟩),
   pushAt 1219 2 1650,
   opAt 1220 .JUMPI]

/-- Instructions 1376..1426, pc 1984..1986. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1221 .POP,
   opAt 1222 .POP,
   opAt 1223 .JUMP]

/-- Instructions 1427..1405, pc 1987..2021. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1224 .JUMPDEST,
   pushAt 1225 2 9344,
   opAt 1226 .MLOAD,
   opAt 1227 (.Dup ⟨0, by decide⟩),
   pushAt 1228 1 64,
   opAt 1229 .ADD,
   opAt 1230 .CALLDATASIZE,
   pushAt 1231 2 8192,
   opAt 1232 .CALLDATACOPY,
   opAt 1233 (.Dup ⟨0, by decide⟩),
   opAt 1234 (.Dup ⟨3, by decide⟩),
   opAt 1235 .ADD,
   pushAt 1236 1 32,
   opAt 1237 (.Swap ⟨0, by decide⟩),
   opAt 1238 .SUB,
   pushAt 1239 1 32,
   opAt 1240 (.Dup ⟨4, by decide⟩),
   opAt 1241 .SUB,
   opAt 1242 (.Swap ⟨3, by decide⟩),
   opAt 1243 .POP,
   opAt 1244 (.Swap ⟨0, by decide⟩),
   opAt 1245 .POP,
   pushAt 1246 1 32,
   opAt 1247 (.Dup ⟨2, by decide⟩),
   opAt 1248 .SUB,
   opAt 1249 (.Swap ⟨1, by decide⟩),
   opAt 1250 .POP]

/-- Instructions 1454..1468, pc 2022..2042. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1251 .JUMPDEST,
   opAt 1252 (.Dup ⟨0, by decide⟩),
   opAt 1253 .MLOAD,
   pushAt 1254 0 0,
   pushAt 1255 2 9440,
   opAt 1256 .MLOAD,
   opAt 1257 (.Dup ⟨4, by decide⟩),
   pushAt 1258 2 9344,
   opAt 1259 .MLOAD,
   opAt 1260 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
