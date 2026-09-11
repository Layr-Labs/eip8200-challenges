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
  [opAt 1148 .POP,
   opAt 1149 .POP,
   pushAt 1150 1 1,
   opAt 1151 .ADD,
   pushAt 1152 2 1507,
   opAt 1153 .JUMP]

/-- Instructions 1320..1332, pc 1850..1875. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1154 .JUMPDEST,
   opAt 1155 .POP,
   pushAt 1156 1 1,
   opAt 1157 (.Dup ⟨1, by decide⟩),
   pushAt 1158 2 3040,
   opAt 1159 .ADD,
   opAt 1160 .MSTORE,
   pushAt 1161 2 1604,
   pushAt 1162 2 1024,
   pushAt 1163 2 3072,
   pushAt 1164 2 1024,
   pushAt 1165 2 3924,
   opAt 1166 .JUMP]

/-- Instructions 1333..1340, pc 1876..1885. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1167 .JUMPDEST,
   opAt 1168 (.Dup ⟨4, by decide⟩),
   opAt 1169 (.Dup ⟨0, by decide⟩),
   opAt 1170 (.Dup ⟨2, by decide⟩),
   pushAt 1171 2 1024,
   opAt 1172 .ADD,
   opAt 1173 .SUB,
   opAt 1174 .RETURN]

/-- Instructions 1341..1344, pc 1886..1891. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1175 .JUMPDEST,
   opAt 1176 .POP,
   pushAt 1177 2 1054,
   opAt 1178 .JUMP]

/-- Instructions 1345..1350, pc 1892..1899. -/
def blk1345 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1179 .JUMPDEST,
   opAt 1180 .POP,
   opAt 1181 .POP,
   opAt 1182 .POP,
   pushAt 1183 2 1054,
   opAt 1184 .JUMP]

/-- Instructions 1351..1359, pc 1900..1910. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1185 .JUMPDEST,
   opAt 1186 .POP,
   opAt 1187 .POP,
   opAt 1188 .POP,
   opAt 1189 .POP,
   opAt 1190 .POP,
   opAt 1191 .POP,
   pushAt 1192 2 1054,
   opAt 1193 .JUMP]

/-- Instructions 1360..1361, pc 1911..1912. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1194 .JUMPDEST,
   pushAt 1195 2 256]

/-- Instructions 1362..1368, pc 1915..1925. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1196 .JUMPDEST,
   pushAt 1197 2 1654,
   opAt 1198 (.Dup ⟨2, by decide⟩),
   opAt 1199 (.Dup ⟨0, by decide⟩),
   opAt 1200 (.Dup ⟨0, by decide⟩),
   pushAt 1201 2 1939,
   opAt 1202 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
