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
  [opAt 1184 .JUMPDEST,
   pushAt 1185 1 1,
   opAt 1186 (.Swap ⟨0, by decide⟩),
   opAt 1187 .SUB,
   opAt 1188 (.Dup ⟨0, by decide⟩),
   pushAt 1189 2 1614,
   opAt 1190 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1191 .POP,
   opAt 1192 .POP,
   opAt 1193 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1194 .JUMPDEST,
   pushAt 1195 2 9344,
   opAt 1196 .MLOAD,
   opAt 1197 (.Dup ⟨0, by decide⟩),
   pushAt 1198 1 64,
   opAt 1199 .ADD,
   opAt 1200 .CALLDATASIZE,
   pushAt 1201 2 8192,
   opAt 1202 .CALLDATACOPY,
   opAt 1203 (.Dup ⟨0, by decide⟩),
   opAt 1204 (.Dup ⟨3, by decide⟩),
   opAt 1205 .ADD,
   pushAt 1206 1 32,
   opAt 1207 (.Swap ⟨0, by decide⟩),
   opAt 1208 .SUB,
   pushAt 1209 1 32,
   opAt 1210 (.Dup ⟨4, by decide⟩),
   opAt 1211 .SUB,
   opAt 1212 (.Swap ⟨3, by decide⟩),
   opAt 1213 .POP,
   opAt 1214 (.Swap ⟨0, by decide⟩),
   opAt 1215 .POP,
   pushAt 1216 1 32,
   opAt 1217 (.Dup ⟨2, by decide⟩),
   opAt 1218 .SUB,
   opAt 1219 (.Swap ⟨1, by decide⟩),
   opAt 1220 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1221 .JUMPDEST,
   opAt 1222 (.Dup ⟨0, by decide⟩),
   opAt 1223 .MLOAD,
   pushAt 1224 0 0,
   pushAt 1225 2 9440,
   opAt 1226 .MLOAD,
   opAt 1227 (.Dup ⟨4, by decide⟩),
   pushAt 1228 2 9344,
   opAt 1229 .MLOAD,
   opAt 1230 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
