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
  [opAt 1296 .POP,
   opAt 1297 .POP,
   pushAt 1298 1 1,
   opAt 1299 .ADD,
   pushAt 1300 2 1751,
   opAt 1301 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1302 .JUMPDEST,
   opAt 1303 .POP,
   pushAt 1304 1 1,
   opAt 1305 (.Dup ⟨1, by decide⟩),
   pushAt 1306 2 3040,
   opAt 1307 .ADD,
   opAt 1308 .MSTORE,
   pushAt 1309 2 1857,
   pushAt 1310 2 1024,
   pushAt 1311 2 3072,
   pushAt 1312 2 1024,
   pushAt 1313 2 4428,
   opAt 1314 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1315 .JUMPDEST,
   opAt 1316 (.Dup ⟨4, by decide⟩),
   opAt 1317 (.Dup ⟨0, by decide⟩),
   opAt 1318 (.Dup ⟨2, by decide⟩),
   pushAt 1319 2 1024,
   opAt 1320 .ADD,
   opAt 1321 .SUB,
   opAt 1322 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1323 .JUMPDEST,
   opAt 1324 .POP,
   pushAt 1325 2 1191,
   opAt 1326 .JUMP]

/-- Instructions 1345..1350, pc 1892..1899. -/
def blk1345 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1327 .JUMPDEST,
   opAt 1328 .POP,
   opAt 1329 .POP,
   opAt 1330 .POP,
   pushAt 1331 2 1191,
   opAt 1332 .JUMP]

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1333 .JUMPDEST,
   opAt 1334 .POP,
   opAt 1335 .POP,
   opAt 1336 .POP,
   opAt 1337 .POP,
   opAt 1338 .POP,
   opAt 1339 .POP,
   pushAt 1340 2 1191,
   opAt 1341 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1342 .JUMPDEST,
   pushAt 1343 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1344 .JUMPDEST,
   pushAt 1345 2 1907,
   opAt 1346 (.Dup ⟨2, by decide⟩),
   opAt 1347 (.Dup ⟨0, by decide⟩),
   opAt 1348 (.Dup ⟨0, by decide⟩),
   pushAt 1349 2 2199,
   opAt 1350 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
