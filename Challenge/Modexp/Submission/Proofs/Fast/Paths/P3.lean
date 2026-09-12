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
  [opAt 1002 .JUMPDEST,
   pushAt 1003 2 9344,
   opAt 1004 .MLOAD,
   pushAt 1005 2 4096,
   pushAt 1006 2 5120,
   opAt 1007 .MCOPY,
   pushAt 1008 2 2849,
   pushAt 1009 2 5120,
   pushAt 1010 2 3273,
   opAt 1011 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1012 .JUMPDEST,
   pushAt 1013 2 1349,
   pushAt 1014 2 6144,
   opAt 1015 (.Dup ⟨0, by decide⟩),
   pushAt 1016 2 6144,
   pushAt 1017 2 3871,
   opAt 1018 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1019 .JUMPDEST,
   opAt 1020 (.Dup ⟨2, by decide⟩),
   opAt 1021 (.Dup ⟨1, by decide⟩),
   opAt 1022 .SHR,
   pushAt 1023 1 1,
   opAt 1024 .AND,
   pushAt 1025 2 1024,
   opAt 1026 .MUL,
   pushAt 1027 2 4096,
   opAt 1028 .ADD,
   pushAt 1029 2 2163,
   opAt 1030 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1031 .JUMPDEST,
   opAt 1032 .POP,
   opAt 1033 (.Dup ⟨0, by decide⟩),
   opAt 1034 .ISZERO,
   pushAt 1035 2 1383,
   opAt 1036 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1037 0 0,
   opAt 1038 .NOT,
   opAt 1039 .ADD,
   pushAt 1040 2 1334,
   opAt 1041 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1042 .JUMPDEST,
   opAt 1043 .POP,
   opAt 1044 (.Dup ⟨2, by decide⟩),
   opAt 1045 .ISZERO,
   pushAt 1046 2 3150,
   opAt 1047 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
