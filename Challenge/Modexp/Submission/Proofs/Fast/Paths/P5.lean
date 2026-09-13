import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 5 (instructions 1385..1395). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1385..1393, pc 1863..1833. -/
def blk1255 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1152 .JUMPDEST,
   opAt 1153 .POP,
   opAt 1154 .POP,
   pushAt 1155 2 3216,
   pushAt 1156 2 512,
   pushAt 1157 2 1536,
   pushAt 1158 2 256,
   pushAt 1159 2 4092,
   opAt 1160 .JUMP]

/-- Instructions 1402..1360, pc 1896..1904. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1161 .JUMPDEST,
   opAt 1162 (.Dup ⟨4, by decide⟩),
   opAt 1163 (.Dup ⟨1, by decide⟩),
   opAt 1164 .EQ,
   pushAt 1165 2 1670,
   opAt 1166 .JUMPI]

/-- Instructions 1409..1416, pc 1905..1914. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1167 2 2229,
   opAt 1168 .JUMP]

/-- Instructions 1423..1423, pc 1916..1932. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1169 .JUMPDEST,
   pushAt 1170 2 1626,
   pushAt 1171 2 256,
   opAt 1172 (.Dup ⟨0, by decide⟩),
   pushAt 1173 2 256,
   pushAt 1174 2 4092,
   opAt 1175 .JUMP]

/-- Instructions 1424..1430, pc 1933..1941. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1176 .JUMPDEST,
   opAt 1177 (.Dup ⟨1, by decide⟩),
   opAt 1178 (.Dup ⟨1, by decide⟩),
   opAt 1179 .AND,
   opAt 1180 .ISZERO,
   pushAt 1181 2 1652,
   opAt 1182 .JUMPI]

/-- Instructions 1431..1388, pc 1942..1957. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1183 2 1651,
   pushAt 1184 2 256,
   pushAt 1185 2 512,
   pushAt 1186 2 256,
   pushAt 1187 2 4092,
   opAt 1188 .JUMP]

/-- Instructions 1389..1389, pc 1958..1958. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1189 .JUMPDEST]

/-- Instructions 1438..1395, pc 1829..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1190 .JUMPDEST,
   pushAt 1191 1 1,
   opAt 1192 .SHR,
   opAt 1193 (.Dup ⟨0, by decide⟩),
   pushAt 1194 2 1611,
   opAt 1195 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
