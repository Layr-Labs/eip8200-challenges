import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 3 (instructions 1186..1242). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1186..1147, pc 1533..1602. -/
def blk1138 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1032 .JUMPDEST,
   pushAt 1033 2 9344,
   opAt 1034 .MLOAD,
   pushAt 1035 2 4096,
   pushAt 1036 2 5120,
   opAt 1037 .MCOPY,
   pushAt 1038 2 2878,
   pushAt 1039 2 5120,
   pushAt 1040 2 3296,
   opAt 1041 .JUMP]

/-- Instructions 1196..1202, pc 1603..1615. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1203..1209, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1042 .JUMPDEST,
   pushAt 1043 2 1385,
   pushAt 1044 2 6144,
   opAt 1045 (.Dup ⟨0, by decide⟩),
   pushAt 1046 2 6144,
   pushAt 1047 2 4055,
   opAt 1048 .JUMP]

/-- Instructions 1210..1221, pc 1634..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1049 .JUMPDEST,
   opAt 1050 (.Dup ⟨2, by decide⟩),
   opAt 1051 (.Dup ⟨1, by decide⟩),
   opAt 1052 .SHR,
   pushAt 1053 1 1,
   opAt 1054 .AND,
   pushAt 1055 2 1024,
   opAt 1056 .MUL,
   pushAt 1057 2 4096,
   opAt 1058 .ADD,
   pushAt 1059 2 2199,
   opAt 1060 .JUMP]

/-- Instructions 1178..1183, pc 1615..1670. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1061 .JUMPDEST,
   opAt 1062 .POP,
   opAt 1063 (.Dup ⟨0, by decide⟩),
   opAt 1064 .ISZERO,
   pushAt 1065 2 1419,
   opAt 1066 .JUMPI]

/-- Instructions 1184..1188, pc 1671..1678. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1067 0 0,
   opAt 1068 .NOT,
   opAt 1069 .ADD,
   pushAt 1070 2 1370,
   opAt 1071 .JUMP]

/-- Instructions 1237..1242, pc 1679..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1072 .JUMPDEST,
   opAt 1073 .POP,
   opAt 1074 (.Dup ⟨2, by decide⟩),
   opAt 1075 .ISZERO,
   pushAt 1076 2 3179,
   opAt 1077 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
