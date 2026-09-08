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
  [opAt 1305 .POP,
   opAt 1306 .POP,
   pushAt 1307 1 1,
   opAt 1308 .ADD,
   pushAt 1309 2 1761,
   opAt 1310 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1311 .JUMPDEST,
   opAt 1312 .POP,
   pushAt 1313 1 1,
   opAt 1314 (.Dup ⟨1, by decide⟩),
   pushAt 1315 2 3040,
   opAt 1316 .ADD,
   opAt 1317 .MSTORE,
   pushAt 1318 2 1867,
   pushAt 1319 2 1024,
   pushAt 1320 2 3072,
   pushAt 1321 2 1024,
   pushAt 1322 2 4432,
   opAt 1323 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1324 .JUMPDEST,
   opAt 1325 (.Dup ⟨4, by decide⟩),
   opAt 1326 (.Dup ⟨0, by decide⟩),
   opAt 1327 (.Dup ⟨2, by decide⟩),
   pushAt 1328 2 1024,
   opAt 1329 .ADD,
   opAt 1330 .SUB,
   opAt 1331 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1332 .JUMPDEST,
   opAt 1333 .POP,
   pushAt 1334 2 1192,
   opAt 1335 .JUMP]

/-- Instructions 1345..1350, pc 1892..1899. -/
def blk1345 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1336 .JUMPDEST,
   opAt 1337 .POP,
   opAt 1338 .POP,
   opAt 1339 .POP,
   pushAt 1340 2 1192,
   opAt 1341 .JUMP]

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1342 .JUMPDEST,
   opAt 1343 .POP,
   opAt 1344 .POP,
   opAt 1345 .POP,
   opAt 1346 .POP,
   opAt 1347 .POP,
   opAt 1348 .POP,
   pushAt 1349 2 1192,
   opAt 1350 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1351 .JUMPDEST,
   pushAt 1352 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1353 .JUMPDEST,
   pushAt 1354 2 1917,
   opAt 1355 (.Dup ⟨2, by decide⟩),
   opAt 1356 (.Dup ⟨0, by decide⟩),
   opAt 1357 (.Dup ⟨0, by decide⟩),
   pushAt 1358 2 2209,
   opAt 1359 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
