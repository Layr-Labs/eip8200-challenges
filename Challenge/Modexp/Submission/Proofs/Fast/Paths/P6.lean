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
  [opAt 1026 .POP,
   opAt 1027 .POP,
   pushAt 1028 1 1,
   opAt 1029 .ADD,
   pushAt 1030 2 1341,
   opAt 1031 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1032 .JUMPDEST,
   opAt 1033 .POP,
   pushAt 1034 1 1,
   opAt 1035 (.Dup ⟨1, by decide⟩),
   pushAt 1036 2 3040,
   opAt 1037 .ADD,
   opAt 1038 .MSTORE,
   pushAt 1039 2 1438,
   pushAt 1040 2 1024,
   pushAt 1041 2 3072,
   pushAt 1042 2 1024,
   pushAt 1043 2 3779,
   opAt 1044 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1045 .JUMPDEST,
   opAt 1046 (.Dup ⟨4, by decide⟩),
   opAt 1047 (.Dup ⟨0, by decide⟩),
   opAt 1048 (.Dup ⟨2, by decide⟩),
   pushAt 1049 2 1024,
   opAt 1050 .ADD,
   opAt 1051 .SUB,
   opAt 1052 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1053 .JUMPDEST,
   opAt 1054 .POP,
   pushAt 1055 2 1100,
   opAt 1056 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1057 .JUMPDEST,
   opAt 1058 .POP,
   opAt 1059 .POP,
   opAt 1060 .POP,
   opAt 1061 .POP,
   opAt 1062 .POP,
   opAt 1063 .POP,
   pushAt 1064 2 1100,
   opAt 1065 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1066 .JUMPDEST,
   pushAt 1067 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1068 .JUMPDEST,
   pushAt 1069 2 1480,
   opAt 1070 (.Dup ⟨2, by decide⟩),
   opAt 1071 (.Dup ⟨0, by decide⟩),
   opAt 1072 (.Dup ⟨0, by decide⟩),
   pushAt 1073 2 1765,
   opAt 1074 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
