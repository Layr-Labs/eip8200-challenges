import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 5 (instructions 1255..1313). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1255..1263, pc 1736..1754. -/
def blk1255 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1159 .JUMPDEST,
   opAt 1160 .POP,
   opAt 1161 .POP,
   pushAt 1162 2 3273,
   pushAt 1163 2 512,
   pushAt 1164 2 1536,
   pushAt 1165 2 256,
   pushAt 1166 2 4047,
   opAt 1167 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1168 .JUMPDEST]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1171 .JUMPDEST,
   opAt 1172 (.Dup ⟨4, by decide⟩),
   opAt 1173 (.Dup ⟨1, by decide⟩),
   opAt 1174 .EQ,
   pushAt 1175 2 1680,
   opAt 1176 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1177 2 2237,
   opAt 1178 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1179 .JUMPDEST,
   pushAt 1180 2 1636,
   pushAt 1181 2 256,
   opAt 1182 (.Dup ⟨0, by decide⟩),
   pushAt 1183 2 256,
   pushAt 1184 2 4047,
   opAt 1185 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1186 .JUMPDEST,
   opAt 1187 (.Dup ⟨1, by decide⟩),
   opAt 1188 (.Dup ⟨1, by decide⟩),
   opAt 1189 .AND,
   opAt 1190 .ISZERO,
   pushAt 1191 2 1662,
   opAt 1192 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1193 2 1661,
   pushAt 1194 2 256,
   pushAt 1195 2 512,
   pushAt 1196 2 256,
   pushAt 1197 2 4047,
   opAt 1198 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1199 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1200 .JUMPDEST,
   pushAt 1201 1 1,
   opAt 1202 .SHR,
   opAt 1203 (.Dup ⟨0, by decide⟩),
   pushAt 1204 2 1621,
   opAt 1205 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
