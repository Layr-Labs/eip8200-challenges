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
  [opAt 1369 .JUMPDEST,
   pushAt 1370 1 1,
   opAt 1371 (.Swap ⟨0, by decide⟩),
   opAt 1372 .SUB,
   opAt 1373 (.Dup ⟨0, by decide⟩),
   pushAt 1374 2 1915,
   opAt 1375 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1376 .POP,
   opAt 1377 .POP,
   opAt 1378 .JUMP]

/-- Entry trampoline, instructions 1379..1381, pc 1939..1943. -/
def blk1379 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1379 .JUMPDEST,
   pushAt 1380 2 5351,
   opAt 1381 .JUMP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1406 .JUMPDEST,
   opAt 1407 (.Dup ⟨0, by decide⟩),
   opAt 1408 .MLOAD,
   pushAt 1409 0 0,
   pushAt 1410 4 9440,
   opAt 1411 .MLOAD,
   opAt 1412 (.Dup ⟨4, by decide⟩),
   pushAt 1413 7 9344,
   opAt 1414 .MLOAD,
   opAt 1415 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
