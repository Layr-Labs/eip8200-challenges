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
  [opAt 997 .JUMPDEST,
   pushAt 998 2 9344,
   opAt 999 .MLOAD,
   pushAt 1000 2 4096,
   pushAt 1001 2 5120,
   opAt 1002 .MCOPY,
   pushAt 1003 2 2837,
   pushAt 1004 2 5120,
   pushAt 1005 2 3261,
   opAt 1006 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1007 .JUMPDEST,
   pushAt 1008 2 1337,
   pushAt 1009 2 6144,
   opAt 1010 (.Dup ⟨0, by decide⟩),
   pushAt 1011 2 6144,
   pushAt 1012 2 3912,
   opAt 1013 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1014 .JUMPDEST,
   opAt 1015 (.Dup ⟨2, by decide⟩),
   opAt 1016 (.Dup ⟨1, by decide⟩),
   opAt 1017 .SHR,
   pushAt 1018 1 1,
   opAt 1019 .AND,
   pushAt 1020 2 1024,
   opAt 1021 .MUL,
   pushAt 1022 2 4096,
   opAt 1023 .ADD,
   pushAt 1024 2 2151,
   opAt 1025 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1026 .JUMPDEST,
   opAt 1027 .POP,
   opAt 1028 (.Dup ⟨0, by decide⟩),
   opAt 1029 .ISZERO,
   pushAt 1030 2 1371,
   opAt 1031 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1032 0 0,
   opAt 1033 .NOT,
   opAt 1034 .ADD,
   pushAt 1035 2 1322,
   opAt 1036 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1037 .JUMPDEST,
   opAt 1038 .POP,
   opAt 1039 (.Dup ⟨2, by decide⟩),
   opAt 1040 .ISZERO,
   pushAt 1041 2 3138,
   opAt 1042 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
