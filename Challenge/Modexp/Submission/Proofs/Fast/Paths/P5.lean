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
  [opAt 1156 .JUMPDEST,
   opAt 1157 .POP,
   opAt 1158 .POP,
   pushAt 1159 2 3216,
   pushAt 1160 2 512,
   pushAt 1161 2 1536,
   pushAt 1162 2 256,
   pushAt 1163 2 4092,
   opAt 1164 .JUMP]

/-- Instructions 1402..1360, pc 1896..1904. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1165 .JUMPDEST,
   opAt 1166 (.Dup ⟨4, by decide⟩),
   opAt 1167 (.Dup ⟨1, by decide⟩),
   opAt 1168 .EQ,
   pushAt 1169 2 1670,
   opAt 1170 .JUMPI]

/-- Instructions 1409..1416, pc 1905..1914. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1171 2 2229,
   opAt 1172 .JUMP]

/-- Instructions 1417..1423, pc 1916..1932. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1173 .JUMPDEST,
   pushAt 1174 2 1626,
   pushAt 1175 2 256,
   opAt 1176 (.Dup ⟨0, by decide⟩),
   pushAt 1177 2 256,
   pushAt 1178 2 4092,
   opAt 1179 .JUMP]

/-- Instructions 1424..1430, pc 1933..1941. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1180 .JUMPDEST,
   opAt 1181 (.Dup ⟨1, by decide⟩),
   opAt 1182 (.Dup ⟨1, by decide⟩),
   opAt 1183 .AND,
   opAt 1184 .ISZERO,
   pushAt 1185 2 1652,
   opAt 1186 .JUMPI]

/-- Instructions 1431..1388, pc 1942..1957. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1187 2 1651,
   pushAt 1188 2 256,
   pushAt 1189 2 512,
   pushAt 1190 2 256,
   pushAt 1191 2 4092,
   opAt 1192 .JUMP]

/-- Instructions 1389..1389, pc 1958..1958. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1193 .JUMPDEST]

/-- Instructions 1438..1395, pc 1829..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1194 .JUMPDEST,
   pushAt 1195 1 1,
   opAt 1196 .SHR,
   opAt 1197 (.Dup ⟨0, by decide⟩),
   pushAt 1198 2 1611,
   opAt 1199 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
