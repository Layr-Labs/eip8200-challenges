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
   pushAt 1138 2 3111,
   pushAt 1139 2 5120,
   pushAt 1140 2 3543,
   opAt 1141 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1142 .JUMPDEST,
   pushAt 1143 2 1565,
   pushAt 1144 2 6144,
   pushAt 1145 2 6144,
   pushAt 1146 2 6144,
   pushAt 1147 2 4137,
   opAt 1148 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1149 .JUMPDEST,
   opAt 1150 (.Dup ⟨2, by decide⟩),
   opAt 1151 (.Dup ⟨1, by decide⟩),
   opAt 1152 .SHR,
   pushAt 1153 1 1,
   opAt 1154 .AND,
   pushAt 1155 2 1024,
   opAt 1156 .MUL,
   pushAt 1157 2 4096,
   opAt 1158 .ADD,
   pushAt 1159 2 2392,
   opAt 1160 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1161 .JUMPDEST,
   opAt 1162 .POP,
   opAt 1163 (.Dup ⟨0, by decide⟩),
   opAt 1164 .ISZERO,
   pushAt 1165 2 1599,
   opAt 1166 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1167 0 0,
   opAt 1168 .NOT,
   opAt 1169 .ADD,
   pushAt 1170 2 1548,
   opAt 1171 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1172 .JUMPDEST,
   opAt 1173 .POP,
   opAt 1174 (.Dup ⟨2, by decide⟩),
   opAt 1175 .ISZERO,
   pushAt 1176 2 3412,
   opAt 1177 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
