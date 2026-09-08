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
  [opAt 1132 .JUMPDEST,
   pushAt 1133 2 9344,
   opAt 1134 .MLOAD,
   pushAt 1135 2 4096,
   pushAt 1136 2 5120,
   opAt 1137 .MCOPY,
   pushAt 1138 2 3054,
   pushAt 1139 2 5120,
   pushAt 1140 2 3498,
   opAt 1141 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 1142 2 9344,
   opAt 1143 .MLOAD,
   pushAt 1144 2 4096,
   pushAt 1145 2 6144,
   opAt 1146 .MCOPY,
   pushAt 1147 1 5]

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1148 .JUMPDEST,
   pushAt 1149 2 1579,
   pushAt 1150 2 6144,
   pushAt 1151 2 6144,
   pushAt 1152 2 6144,
   pushAt 1153 2 4176,
   opAt 1154 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1155 .JUMPDEST,
   opAt 1156 (.Dup ⟨2, by decide⟩),
   opAt 1157 (.Dup ⟨1, by decide⟩),
   opAt 1158 .SHR,
   pushAt 1159 1 1,
   opAt 1160 .AND,
   pushAt 1161 2 1024,
   opAt 1162 .MUL,
   pushAt 1163 2 4096,
   opAt 1164 .ADD,
   pushAt 1165 2 2585,
   opAt 1166 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1171 .JUMPDEST,
   opAt 1172 .POP,
   opAt 1173 (.Dup ⟨0, by decide⟩),
   opAt 1174 .ISZERO,
   pushAt 1175 2 1624,
   opAt 1176 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1177 0 0,
   opAt 1178 .NOT,
   opAt 1179 .ADD,
   pushAt 1180 3 1562,
   opAt 1181 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1182 .JUMPDEST,
   opAt 1183 .POP,
   opAt 1184 (.Dup ⟨2, by decide⟩),
   opAt 1185 .ISZERO,
   pushAt 1186 2 1748,
   opAt 1187 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
