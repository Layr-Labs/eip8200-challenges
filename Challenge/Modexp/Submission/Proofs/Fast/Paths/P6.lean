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
  [opAt 1224 .POP,
   opAt 1225 .POP,
   pushAt 1226 1 1,
   opAt 1227 .ADD,
   pushAt 1228 2 1622,
   opAt 1229 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1230 .JUMPDEST,
   opAt 1231 .POP,
   pushAt 1232 1 1,
   opAt 1233 (.Dup ⟨1, by decide⟩),
   pushAt 1234 2 3040,
   opAt 1235 .ADD,
   opAt 1236 .MSTORE,
   pushAt 1237 2 1721,
   pushAt 1238 2 1024,
   pushAt 1239 2 3072,
   pushAt 1240 2 1024,
   pushAt 1241 2 4049,
   opAt 1242 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1243 .JUMPDEST,
   opAt 1244 (.Dup ⟨4, by decide⟩),
   opAt 1245 (.Dup ⟨0, by decide⟩),
   opAt 1246 (.Dup ⟨2, by decide⟩),
   pushAt 1247 2 1024,
   opAt 1248 .ADD,
   opAt 1249 .SUB,
   opAt 1250 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1251 .JUMPDEST,
   opAt 1252 .POP,
   pushAt 1253 2 1134,
   opAt 1254 .JUMP]

/-- Instructions 1345..1350, pc 1892..1899. -/
def blk1345 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1255 .JUMPDEST,
   opAt 1256 .POP,
   opAt 1257 .POP,
   opAt 1258 .POP,
   pushAt 1259 2 1134,
   opAt 1260 .JUMP]

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1261 .JUMPDEST,
   opAt 1262 .POP,
   opAt 1263 .POP,
   opAt 1264 .POP,
   opAt 1265 .POP,
   opAt 1266 .POP,
   opAt 1267 .POP,
   pushAt 1268 2 1134,
   opAt 1269 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1270 .JUMPDEST,
   pushAt 1271 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1272 .JUMPDEST,
   pushAt 1273 2 1771,
   opAt 1274 (.Dup ⟨2, by decide⟩),
   opAt 1275 (.Dup ⟨0, by decide⟩),
   opAt 1276 (.Dup ⟨0, by decide⟩),
   pushAt 1277 2 2056,
   opAt 1278 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
