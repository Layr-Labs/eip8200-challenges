import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1369..1420). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1369..1375, pc 1926..1935. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1203 .JUMPDEST,
   pushAt 1204 1 1,
   opAt 1205 (.Swap ⟨0, by decide⟩),
   opAt 1206 .SUB,
   opAt 1207 (.Dup ⟨0, by decide⟩),
   pushAt 1208 2 1643,
   opAt 1209 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1210 .POP,
   opAt 1211 .POP,
   opAt 1212 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1213 .JUMPDEST,
   pushAt 1214 2 2784,
   opAt 1215 .MLOAD,
   opAt 1216 (.Dup ⟨0, by decide⟩),
   pushAt 1217 1 64,
   opAt 1218 .ADD,
   opAt 1219 .CALLDATASIZE,
   pushAt 1220 2 2048,
   opAt 1221 .CALLDATACOPY,
   opAt 1222 (.Dup ⟨0, by decide⟩),
   opAt 1223 (.Dup ⟨3, by decide⟩),
   opAt 1224 .ADD,
   pushAt 1225 1 32,
   opAt 1226 (.Swap ⟨0, by decide⟩),
   opAt 1227 .SUB,
   pushAt 1228 1 32,
   opAt 1229 (.Dup ⟨4, by decide⟩),
   opAt 1230 .SUB,
   opAt 1231 (.Swap ⟨3, by decide⟩),
   opAt 1232 .POP,
   opAt 1233 (.Swap ⟨0, by decide⟩),
   opAt 1234 .POP,
   pushAt 1235 1 32,
   opAt 1236 (.Dup ⟨2, by decide⟩),
   opAt 1237 .SUB,
   opAt 1238 (.Swap ⟨1, by decide⟩),
   opAt 1239 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1240 .JUMPDEST,
   opAt 1241 (.Dup ⟨0, by decide⟩),
   opAt 1242 .MLOAD,
   pushAt 1243 0 0,
   pushAt 1244 2 2880,
   opAt 1245 .MLOAD,
   opAt 1246 (.Dup ⟨4, by decide⟩),
   pushAt 1247 2 2784,
   opAt 1248 .MLOAD,
   opAt 1249 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
