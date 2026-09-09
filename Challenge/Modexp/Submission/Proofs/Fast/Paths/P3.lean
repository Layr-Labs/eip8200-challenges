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
  [opAt 1134 .JUMPDEST,
   pushAt 1135 2 9344,
   opAt 1136 .MLOAD,
   pushAt 1137 2 4096,
   pushAt 1138 2 5120,
   opAt 1139 .MCOPY,
   pushAt 1140 2 3294,
   pushAt 1141 2 5120,
   pushAt 1142 2 3739,
   opAt 1143 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1144 .JUMPDEST,
   pushAt 1145 2 9344,
   opAt 1146 .MLOAD,
   pushAt 1147 2 4096,
   pushAt 1148 2 6144,
   opAt 1149 .MCOPY,
   pushAt 1150 1 5]

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1151 .JUMPDEST,
   pushAt 1152 2 1581,
   pushAt 1153 2 6144,
   pushAt 1154 2 6144,
   pushAt 1155 2 6144,
   pushAt 1156 2 4428,
   opAt 1157 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1158 .JUMPDEST,
   opAt 1159 (.Dup ⟨2, by decide⟩),
   opAt 1160 (.Dup ⟨1, by decide⟩),
   opAt 1161 .SHR,
   pushAt 1162 1 1,
   opAt 1163 .AND,
   pushAt 1164 2 1024,
   opAt 1165 .MUL,
   pushAt 1166 2 4096,
   opAt 1167 .ADD,
   pushAt 1168 2 2584,
   opAt 1169 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1174 .JUMPDEST,
   opAt 1175 .POP,
   opAt 1176 (.Dup ⟨0, by decide⟩),
   opAt 1177 .ISZERO,
   pushAt 1178 2 1622,
   opAt 1179 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1180 0 0,
   opAt 1181 .NOT,
   opAt 1182 .ADD,
   pushAt 1183 2 1564,
   opAt 1184 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1185 .JUMPDEST,
   opAt 1186 .POP,
   opAt 1187 (.Dup ⟨2, by decide⟩),
   opAt 1188 .ISZERO,
   pushAt 1189 2 1747,
   opAt 1190 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
