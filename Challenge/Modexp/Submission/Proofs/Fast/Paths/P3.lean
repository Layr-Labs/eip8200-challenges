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
  [opAt 1130 .JUMPDEST,
   pushAt 1131 2 9344,
   opAt 1132 .MLOAD,
   pushAt 1133 2 4096,
   pushAt 1134 2 5120,
   opAt 1135 .MCOPY,
   pushAt 1136 2 3330,
   pushAt 1137 2 5120,
   pushAt 1138 2 3775,
   opAt 1139 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1140 .JUMPDEST,
   pushAt 1141 2 9344,
   opAt 1142 .MLOAD,
   pushAt 1143 2 4096,
   pushAt 1144 2 6144,
   opAt 1145 .MCOPY,
   pushAt 1146 1 5]

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1147 .JUMPDEST,
   pushAt 1148 2 1586,
   pushAt 1149 2 6144,
   pushAt 1150 2 6144,
   pushAt 1151 2 6144,
   pushAt 1152 2 4465,
   opAt 1153 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1154 .JUMPDEST,
   opAt 1155 (.Dup ⟨2, by decide⟩),
   opAt 1156 (.Dup ⟨1, by decide⟩),
   opAt 1157 .SHR,
   pushAt 1158 1 1,
   opAt 1159 .AND,
   pushAt 1160 2 1024,
   opAt 1161 .MUL,
   pushAt 1162 2 4096,
   opAt 1163 .ADD,
   pushAt 1164 2 2604,
   opAt 1165 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1170 .JUMPDEST,
   opAt 1171 .POP,
   opAt 1172 (.Dup ⟨0, by decide⟩),
   opAt 1173 .ISZERO,
   pushAt 1174 2 1631,
   opAt 1175 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1176 0 0,
   opAt 1177 .NOT,
   opAt 1178 .ADD,
   pushAt 1179 3 1569,
   opAt 1180 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1181 .JUMPDEST,
   opAt 1182 .POP,
   opAt 1183 (.Dup ⟨2, by decide⟩),
   opAt 1184 .ISZERO,
   pushAt 1185 2 1756,
   opAt 1186 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
