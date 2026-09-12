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
  [opAt 1158 .JUMPDEST,
   opAt 1159 .POP,
   opAt 1160 .POP,
   pushAt 1161 2 1604,
   pushAt 1162 2 2048,
   pushAt 1163 2 6144,
   pushAt 1164 2 1024,
   pushAt 1165 2 4047,
   opAt 1166 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1167 .JUMPDEST]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1170 .JUMPDEST,
   opAt 1171 (.Dup ⟨4, by decide⟩),
   opAt 1172 (.Dup ⟨1, by decide⟩),
   opAt 1173 .EQ,
   pushAt 1174 2 1680,
   opAt 1175 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1176 2 2237,
   opAt 1177 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1178 .JUMPDEST,
   pushAt 1179 2 1636,
   pushAt 1180 2 1024,
   opAt 1181 (.Dup ⟨0, by decide⟩),
   pushAt 1182 2 1024,
   pushAt 1183 2 4047,
   opAt 1184 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1185 .JUMPDEST,
   opAt 1186 (.Dup ⟨1, by decide⟩),
   opAt 1187 (.Dup ⟨1, by decide⟩),
   opAt 1188 .AND,
   opAt 1189 .ISZERO,
   pushAt 1190 2 1662,
   opAt 1191 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1192 2 1661,
   pushAt 1193 2 1024,
   pushAt 1194 2 2048,
   pushAt 1195 2 1024,
   pushAt 1196 2 4047,
   opAt 1197 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1198 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1199 .JUMPDEST,
   pushAt 1200 1 1,
   opAt 1201 .SHR,
   opAt 1202 (.Dup ⟨0, by decide⟩),
   pushAt 1203 2 1621,
   opAt 1204 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
