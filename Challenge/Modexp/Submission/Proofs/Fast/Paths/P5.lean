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
  [opAt 1151 .JUMPDEST,
   opAt 1152 .POP,
   opAt 1153 .POP,
   pushAt 1154 2 3216,
   pushAt 1155 2 512,
   pushAt 1156 2 1536,
   pushAt 1157 2 256,
   pushAt 1158 2 4092,
   opAt 1159 .JUMP]

/-- Instructions 1402..1360, pc 1896..1904. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1160 .JUMPDEST,
   opAt 1161 (.Dup ⟨4, by decide⟩),
   opAt 1162 (.Dup ⟨1, by decide⟩),
   opAt 1163 .EQ,
   pushAt 1164 2 1670,
   opAt 1165 .JUMPI]

/-- Instructions 1409..1416, pc 1905..1914. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1166 2 2229,
   opAt 1167 .JUMP]

/-- Instructions 1423..1423, pc 1916..1932. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1168 .JUMPDEST,
   pushAt 1169 2 1626,
   pushAt 1170 2 256,
   opAt 1171 (.Dup ⟨0, by decide⟩),
   pushAt 1172 2 256,
   pushAt 1173 2 4092,
   opAt 1174 .JUMP]

/-- Instructions 1424..1430, pc 1933..1941. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1175 .JUMPDEST,
   opAt 1176 (.Dup ⟨1, by decide⟩),
   opAt 1177 (.Dup ⟨1, by decide⟩),
   opAt 1178 .AND,
   opAt 1179 .ISZERO,
   pushAt 1180 2 1652,
   opAt 1181 .JUMPI]

/-- Instructions 1431..1388, pc 1942..1957. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1182 2 1651,
   pushAt 1183 2 256,
   pushAt 1184 2 512,
   pushAt 1185 2 256,
   pushAt 1186 2 4092,
   opAt 1187 .JUMP]

/-- Instructions 1389..1389, pc 1958..1958. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1188 .JUMPDEST]

/-- Instructions 1438..1395, pc 1829..1888. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1189 .JUMPDEST,
   pushAt 1190 1 1,
   opAt 1191 .SHR,
   opAt 1192 (.Dup ⟨0, by decide⟩),
   pushAt 1193 2 1611,
   opAt 1194 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
