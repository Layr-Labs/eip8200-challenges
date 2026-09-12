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
  [opAt 1128 .POP,
   opAt 1129 .POP,
   pushAt 1130 1 1,
   opAt 1131 .ADD,
   pushAt 1132 2 1470,
   opAt 1133 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1134 .JUMPDEST,
   opAt 1135 .POP,
   pushAt 1136 1 1,
   opAt 1137 (.Dup ⟨1, by decide⟩),
   pushAt 1138 2 3040,
   opAt 1139 .ADD,
   opAt 1140 .MSTORE,
   pushAt 1141 2 1567,
   pushAt 1142 2 1024,
   pushAt 1143 2 3072,
   pushAt 1144 2 1024,
   pushAt 1145 2 3900,
   opAt 1146 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1147 .JUMPDEST,
   opAt 1148 (.Dup ⟨4, by decide⟩),
   opAt 1149 (.Dup ⟨0, by decide⟩),
   opAt 1150 (.Dup ⟨2, by decide⟩),
   pushAt 1151 2 1024,
   opAt 1152 .ADD,
   opAt 1153 .SUB,
   opAt 1154 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1155 .JUMPDEST,
   opAt 1156 .POP,
   pushAt 1157 2 1054,
   opAt 1158 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1159 .JUMPDEST,
   opAt 1160 .POP,
   opAt 1161 .POP,
   opAt 1162 .POP,
   opAt 1163 .POP,
   opAt 1164 .POP,
   opAt 1165 .POP,
   pushAt 1166 2 1054,
   opAt 1167 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1168 .JUMPDEST,
   pushAt 1169 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1170 .JUMPDEST,
   pushAt 1171 2 1609,
   opAt 1172 (.Dup ⟨2, by decide⟩),
   opAt 1173 (.Dup ⟨0, by decide⟩),
   opAt 1174 (.Dup ⟨0, by decide⟩),
   pushAt 1175 2 1894,
   opAt 1176 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
