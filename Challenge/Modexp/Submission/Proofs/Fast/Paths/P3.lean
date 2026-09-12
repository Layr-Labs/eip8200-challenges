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
  [opAt 995 .JUMPDEST,
   pushAt 996 2 9344,
   opAt 997 .MLOAD,
   pushAt 998 2 4096,
   pushAt 999 2 5120,
   opAt 1000 .MCOPY,
   pushAt 1001 2 2829,
   pushAt 1002 2 5120,
   pushAt 1003 2 3249,
   opAt 1004 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1005 .JUMPDEST,
   pushAt 1006 2 1333,
   pushAt 1007 2 6144,
   opAt 1008 (.Dup ⟨0, by decide⟩),
   pushAt 1009 2 6144,
   pushAt 1010 2 3900,
   opAt 1011 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1012 .JUMPDEST,
   opAt 1013 (.Dup ⟨2, by decide⟩),
   opAt 1014 (.Dup ⟨1, by decide⟩),
   opAt 1015 .SHR,
   pushAt 1016 1 1,
   opAt 1017 .AND,
   pushAt 1018 2 1024,
   opAt 1019 .MUL,
   pushAt 1020 2 4096,
   opAt 1021 .ADD,
   pushAt 1022 2 2147,
   opAt 1023 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1024 .JUMPDEST,
   opAt 1025 .POP,
   opAt 1026 (.Dup ⟨0, by decide⟩),
   opAt 1027 .ISZERO,
   pushAt 1028 2 1367,
   opAt 1029 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1030 0 0,
   opAt 1031 .NOT,
   opAt 1032 .ADD,
   pushAt 1033 2 1318,
   opAt 1034 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1035 .JUMPDEST,
   opAt 1036 .POP,
   opAt 1037 (.Dup ⟨2, by decide⟩),
   opAt 1038 .ISZERO,
   pushAt 1039 2 3130,
   opAt 1040 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
