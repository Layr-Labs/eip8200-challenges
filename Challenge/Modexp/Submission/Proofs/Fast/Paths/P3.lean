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
  [opAt 1133 .JUMPDEST,
   pushAt 1134 2 9344,
   opAt 1135 .MLOAD,
   pushAt 1136 2 4096,
   pushAt 1137 2 5120,
   opAt 1138 .MCOPY,
   pushAt 1139 2 3533,
   pushAt 1140 2 5120,
   pushAt 1141 2 3978,
   opAt 1142 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1143 .JUMPDEST,
   pushAt 1144 2 9344,
   opAt 1145 .MLOAD,
   pushAt 1146 2 4096,
   pushAt 1147 2 6144,
   opAt 1148 .MCOPY,
   pushAt 1149 1 5]

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1150 .JUMPDEST,
   pushAt 1151 2 1580,
   pushAt 1152 2 6144,
   pushAt 1153 2 6144,
   pushAt 1154 2 6144,
   pushAt 1155 2 4751,
   opAt 1156 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1157 .JUMPDEST,
   opAt 1158 (.Dup ⟨2, by decide⟩),
   opAt 1159 (.Dup ⟨1, by decide⟩),
   opAt 1160 .SHR,
   pushAt 1161 1 1,
   opAt 1162 .AND,
   pushAt 1163 2 1024,
   opAt 1164 .MUL,
   pushAt 1165 2 4096,
   opAt 1166 .ADD,
   pushAt 1167 2 2933,
   opAt 1168 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1173 .JUMPDEST,
   opAt 1174 .POP,
   opAt 1175 (.Dup ⟨0, by decide⟩),
   opAt 1176 .ISZERO,
   pushAt 1177 2 1619,
   opAt 1178 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1179 0 0,
   opAt 1180 .NOT,
   opAt 1181 .ADD,
   pushAt 1182 3 1563,
   opAt 1183 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1184 .JUMPDEST,
   opAt 1185 .POP,
   opAt 1186 (.Dup ⟨2, by decide⟩),
   opAt 1187 .ISZERO,
   pushAt 1188 2 1737,
   opAt 1189 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
