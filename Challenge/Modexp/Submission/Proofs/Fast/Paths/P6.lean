import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 6 (instructions 1314..1368). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1314..1319, pc 1841..1849. -/
def blk1314 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1130 .POP,
   opAt 1131 .POP,
   pushAt 1132 1 1,
   opAt 1133 .ADD,
   pushAt 1134 2 1474,
   opAt 1135 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1136 .JUMPDEST,
   opAt 1137 .POP,
   pushAt 1138 1 1,
   opAt 1139 (.Dup ⟨1, by decide⟩),
   pushAt 1140 2 736,
   opAt 1141 .ADD,
   opAt 1142 .MSTORE,
   pushAt 1143 2 1571,
   pushAt 1144 2 256,
   pushAt 1145 2 768,
   pushAt 1146 2 256,
   pushAt 1147 2 3912,
   opAt 1148 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1149 .JUMPDEST,
   opAt 1150 (.Dup ⟨4, by decide⟩),
   opAt 1151 (.Dup ⟨0, by decide⟩),
   opAt 1152 (.Dup ⟨2, by decide⟩),
   pushAt 1153 2 256,
   opAt 1154 .ADD,
   opAt 1155 .SUB,
   opAt 1156 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1157 .JUMPDEST,
   opAt 1158 .POP,
   pushAt 1159 2 1054,
   opAt 1160 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1161 .JUMPDEST,
   opAt 1162 .POP,
   opAt 1163 .POP,
   opAt 1164 .POP,
   opAt 1165 .POP,
   opAt 1166 .POP,
   opAt 1167 .POP,
   pushAt 1168 2 1054,
   opAt 1169 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1170 .JUMPDEST,
   pushAt 1171 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1172 .JUMPDEST,
   pushAt 1173 2 1613,
   opAt 1174 (.Dup ⟨2, by decide⟩),
   opAt 1175 (.Dup ⟨0, by decide⟩),
   opAt 1176 (.Dup ⟨0, by decide⟩),
   pushAt 1177 2 1898,
   opAt 1178 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
