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
   pushAt 1138 2 3294,
   pushAt 1139 2 5120,
   pushAt 1140 2 3739,
   opAt 1141 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1142 .JUMPDEST,
   pushAt 1143 2 9344,
   opAt 1144 .MLOAD,
   pushAt 1145 2 4096,
   pushAt 1146 2 6144,
   opAt 1147 .MCOPY,
   pushAt 1148 1 5]

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1149 .JUMPDEST,
   pushAt 1150 2 1581,
   pushAt 1151 2 6144,
   pushAt 1152 2 6144,
   pushAt 1153 2 6144,
   pushAt 1154 2 4424,
   opAt 1155 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1156 .JUMPDEST,
   opAt 1157 (.Dup ⟨2, by decide⟩),
   opAt 1158 (.Dup ⟨1, by decide⟩),
   opAt 1159 .SHR,
   pushAt 1160 1 1,
   opAt 1161 .AND,
   pushAt 1162 2 1024,
   opAt 1163 .MUL,
   pushAt 1164 2 4096,
   opAt 1165 .ADD,
   pushAt 1166 2 2584,
   opAt 1167 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1172 .JUMPDEST,
   opAt 1173 .POP,
   opAt 1174 (.Dup ⟨0, by decide⟩),
   opAt 1175 .ISZERO,
   pushAt 1176 2 1622,
   opAt 1177 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1178 0 0,
   opAt 1179 .NOT,
   opAt 1180 .ADD,
   pushAt 1181 2 1564,
   opAt 1182 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1183 .JUMPDEST,
   opAt 1184 .POP,
   opAt 1185 (.Dup ⟨2, by decide⟩),
   opAt 1186 .ISZERO,
   pushAt 1187 2 1747,
   opAt 1188 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
