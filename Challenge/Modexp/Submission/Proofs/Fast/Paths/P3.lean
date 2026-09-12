import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 3 (instructions 1138..1194). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1138..1147, pc 1533..1554. -/
def blk1138 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1015 .JUMPDEST,
   pushAt 1016 2 9344,
   opAt 1017 .MLOAD,
   pushAt 1018 2 4096,
   pushAt 1019 2 5120,
   opAt 1020 .MCOPY,
   pushAt 1021 2 2878,
   pushAt 1022 2 5120,
   pushAt 1023 2 3296,
   opAt 1024 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1025 .JUMPDEST,
   pushAt 1026 2 1370,
   pushAt 1027 2 6144,
   opAt 1028 (.Dup ⟨0, by decide⟩),
   pushAt 1029 2 6144,
   pushAt 1030 2 3920,
   opAt 1031 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1032 .JUMPDEST,
   opAt 1033 (.Dup ⟨2, by decide⟩),
   opAt 1034 (.Dup ⟨1, by decide⟩),
   opAt 1035 .SHR,
   pushAt 1036 1 1,
   opAt 1037 .AND,
   pushAt 1038 2 1024,
   opAt 1039 .MUL,
   pushAt 1040 2 4096,
   opAt 1041 .ADD,
   pushAt 1042 2 2192,
   opAt 1043 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1044 .JUMPDEST,
   opAt 1045 .POP,
   opAt 1046 (.Dup ⟨0, by decide⟩),
   opAt 1047 .ISZERO,
   pushAt 1048 2 1404,
   opAt 1049 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1050 0 0,
   opAt 1051 .NOT,
   opAt 1052 .ADD,
   pushAt 1053 2 1355,
   opAt 1054 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1055 .JUMPDEST,
   opAt 1056 .POP,
   opAt 1057 (.Dup ⟨2, by decide⟩),
   opAt 1058 .ISZERO,
   pushAt 1059 2 3179,
   opAt 1060 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
