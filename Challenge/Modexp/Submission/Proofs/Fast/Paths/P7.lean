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
  [opAt 1179 .JUMPDEST,
   pushAt 1180 1 1,
   opAt 1181 (.Swap ⟨0, by decide⟩),
   opAt 1182 .SUB,
   opAt 1183 (.Dup ⟨0, by decide⟩),
   pushAt 1184 2 1602,
   opAt 1185 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1186 .POP,
   opAt 1187 .POP,
   opAt 1188 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1189 .JUMPDEST,
   pushAt 1190 2 5248,
   opAt 1191 .MLOAD,
   opAt 1192 (.Dup ⟨0, by decide⟩),
   pushAt 1193 1 64,
   opAt 1194 .ADD,
   opAt 1195 .CALLDATASIZE,
   pushAt 1196 2 4096,
   opAt 1197 .CALLDATACOPY,
   opAt 1198 (.Dup ⟨0, by decide⟩),
   opAt 1199 (.Dup ⟨3, by decide⟩),
   opAt 1200 .ADD,
   pushAt 1201 1 32,
   opAt 1202 (.Swap ⟨0, by decide⟩),
   opAt 1203 .SUB,
   pushAt 1204 1 32,
   opAt 1205 (.Dup ⟨4, by decide⟩),
   opAt 1206 .SUB,
   opAt 1207 (.Swap ⟨3, by decide⟩),
   opAt 1208 .POP,
   opAt 1209 (.Swap ⟨0, by decide⟩),
   opAt 1210 .POP,
   pushAt 1211 1 32,
   opAt 1212 (.Dup ⟨2, by decide⟩),
   opAt 1213 .SUB,
   opAt 1214 (.Swap ⟨1, by decide⟩),
   opAt 1215 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1216 .JUMPDEST,
   opAt 1217 (.Dup ⟨0, by decide⟩),
   opAt 1218 .MLOAD,
   pushAt 1219 0 0,
   pushAt 1220 2 5344,
   opAt 1221 .MLOAD,
   opAt 1222 (.Dup ⟨4, by decide⟩),
   pushAt 1223 2 5248,
   opAt 1224 .MLOAD,
   opAt 1225 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
