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
  [opAt 1123 .JUMPDEST,
   pushAt 1124 2 9344,
   opAt 1125 .MLOAD,
   pushAt 1126 2 4096,
   pushAt 1127 2 5120,
   opAt 1128 .MCOPY,
   pushAt 1129 2 3298,
   pushAt 1130 2 5120,
   pushAt 1131 2 3739,
   opAt 1132 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1133 2 9344,
   opAt 1134 .MLOAD,
   pushAt 1135 2 4096,
   pushAt 1136 2 6144,
   opAt 1137 .MCOPY,
   pushAt 1138 1 5]

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1139 .JUMPDEST,
   pushAt 1140 2 1569,
   pushAt 1141 2 6144,
   pushAt 1142 2 6144,
   pushAt 1143 2 6144,
   pushAt 1144 2 4428,
   opAt 1145 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1146 .JUMPDEST,
   opAt 1147 (.Dup ⟨2, by decide⟩),
   opAt 1148 (.Dup ⟨1, by decide⟩),
   opAt 1149 .SHR,
   pushAt 1150 1 1,
   opAt 1151 .AND,
   pushAt 1152 2 1024,
   opAt 1153 .MUL,
   pushAt 1154 2 4096,
   opAt 1155 .ADD,
   pushAt 1156 2 2575,
   opAt 1157 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1162 .JUMPDEST,
   opAt 1163 .POP,
   opAt 1164 (.Dup ⟨0, by decide⟩),
   opAt 1165 .ISZERO,
   pushAt 1166 2 1614,
   opAt 1167 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1168 0 0,
   opAt 1169 .NOT,
   opAt 1170 .ADD,
   pushAt 1171 3 1552,
   opAt 1172 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1173 .JUMPDEST,
   opAt 1174 .POP,
   opAt 1175 (.Dup ⟨2, by decide⟩),
   opAt 1176 .ISZERO,
   pushAt 1177 2 1738,
   opAt 1178 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
