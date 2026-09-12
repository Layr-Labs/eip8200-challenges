import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 6 (instructions 1314..1368). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1314..1319, pc 1841..1849. -/
def blk1314 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1206 .POP,
   opAt 1207 .POP,
   pushAt 1208 1 1,
   opAt 1209 .ADD,
   pushAt 1210 2 1609,
   opAt 1211 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1212 .JUMPDEST,
   opAt 1213 .POP,
   pushAt 1214 1 1,
   opAt 1215 (.Dup ⟨1, by decide⟩),
   pushAt 1216 2 736,
   opAt 1217 .ADD,
   opAt 1218 .MSTORE,
   pushAt 1219 2 1706,
   pushAt 1220 2 256,
   pushAt 1221 2 768,
   pushAt 1222 2 256,
   pushAt 1223 2 4047,
   opAt 1224 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1225 .JUMPDEST,
   opAt 1226 (.Dup ⟨4, by decide⟩),
   opAt 1227 (.Dup ⟨0, by decide⟩),
   opAt 1228 (.Dup ⟨2, by decide⟩),
   pushAt 1229 2 256,
   opAt 1230 .ADD,
   opAt 1231 .SUB,
   opAt 1232 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1233 .JUMPDEST,
   opAt 1234 .POP,
   pushAt 1235 2 1189,
   opAt 1236 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1237 .JUMPDEST,
   opAt 1238 .POP,
   opAt 1239 .POP,
   opAt 1240 .POP,
   opAt 1241 .POP,
   opAt 1242 .POP,
   opAt 1243 .POP,
   pushAt 1244 2 1189,
   opAt 1245 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1246 .JUMPDEST,
   pushAt 1247 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1248 .JUMPDEST,
   pushAt 1249 2 1748,
   opAt 1250 (.Dup ⟨2, by decide⟩),
   opAt 1251 (.Dup ⟨0, by decide⟩),
   opAt 1252 (.Dup ⟨0, by decide⟩),
   pushAt 1253 2 2033,
   opAt 1254 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
