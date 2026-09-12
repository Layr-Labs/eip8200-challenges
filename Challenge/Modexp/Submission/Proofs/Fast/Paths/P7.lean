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
  [opAt 1177 .JUMPDEST,
   pushAt 1178 1 1,
   opAt 1179 (.Swap ⟨0, by decide⟩),
   opAt 1180 .SUB,
   opAt 1181 (.Dup ⟨0, by decide⟩),
   pushAt 1182 2 1598,
   opAt 1183 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1184 .POP,
   opAt 1185 .POP,
   opAt 1186 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1187 .JUMPDEST,
   pushAt 1188 2 9344,
   opAt 1189 .MLOAD,
   opAt 1190 (.Dup ⟨0, by decide⟩),
   pushAt 1191 1 64,
   opAt 1192 .ADD,
   opAt 1193 .CALLDATASIZE,
   pushAt 1194 2 8192,
   opAt 1195 .CALLDATACOPY,
   opAt 1196 (.Dup ⟨0, by decide⟩),
   opAt 1197 (.Dup ⟨3, by decide⟩),
   opAt 1198 .ADD,
   pushAt 1199 1 32,
   opAt 1200 (.Swap ⟨0, by decide⟩),
   opAt 1201 .SUB,
   pushAt 1202 1 32,
   opAt 1203 (.Dup ⟨4, by decide⟩),
   opAt 1204 .SUB,
   opAt 1205 (.Swap ⟨3, by decide⟩),
   opAt 1206 .POP,
   opAt 1207 (.Swap ⟨0, by decide⟩),
   opAt 1208 .POP,
   pushAt 1209 1 32,
   opAt 1210 (.Dup ⟨2, by decide⟩),
   opAt 1211 .SUB,
   opAt 1212 (.Swap ⟨1, by decide⟩),
   opAt 1213 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1214 .JUMPDEST,
   opAt 1215 (.Dup ⟨0, by decide⟩),
   opAt 1216 .MLOAD,
   pushAt 1217 0 0,
   pushAt 1218 2 9440,
   opAt 1219 .MLOAD,
   opAt 1220 (.Dup ⟨4, by decide⟩),
   pushAt 1221 2 9344,
   opAt 1222 .MLOAD,
   opAt 1223 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
