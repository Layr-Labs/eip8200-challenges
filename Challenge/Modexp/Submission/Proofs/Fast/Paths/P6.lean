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
  [opAt 1135 .POP,
   opAt 1136 .POP,
   pushAt 1137 1 1,
   opAt 1138 .ADD,
   pushAt 1139 2 1486,
   opAt 1140 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1141 .JUMPDEST,
   opAt 1142 .POP,
   pushAt 1143 1 1,
   opAt 1144 (.Dup ⟨1, by decide⟩),
   pushAt 1145 2 3040,
   opAt 1146 .ADD,
   opAt 1147 .MSTORE,
   pushAt 1148 2 1583,
   pushAt 1149 2 1024,
   pushAt 1150 2 3072,
   pushAt 1151 2 1024,
   pushAt 1152 2 3862,
   opAt 1153 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1154 .JUMPDEST,
   opAt 1155 (.Dup ⟨4, by decide⟩),
   opAt 1156 (.Dup ⟨0, by decide⟩),
   opAt 1157 (.Dup ⟨2, by decide⟩),
   pushAt 1158 2 1024,
   opAt 1159 .ADD,
   opAt 1160 .SUB,
   opAt 1161 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1162 .JUMPDEST,
   opAt 1163 .POP,
   pushAt 1164 2 1054,
   opAt 1165 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1166 .JUMPDEST,
   opAt 1167 .POP,
   opAt 1168 .POP,
   opAt 1169 .POP,
   opAt 1170 .POP,
   opAt 1171 .POP,
   opAt 1172 .POP,
   pushAt 1173 2 1054,
   opAt 1174 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1175 .JUMPDEST,
   pushAt 1176 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1177 .JUMPDEST,
   pushAt 1178 2 1625,
   opAt 1179 (.Dup ⟨2, by decide⟩),
   opAt 1180 (.Dup ⟨0, by decide⟩),
   opAt 1181 (.Dup ⟨0, by decide⟩),
   pushAt 1182 2 1910,
   opAt 1183 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
