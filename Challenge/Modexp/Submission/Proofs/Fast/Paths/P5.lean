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
  [opAt 1218 .JUMPDEST,
   opAt 1219 .POP,
   opAt 1220 .POP,
   pushAt 1221 2 1697,
   pushAt 1222 2 2048,
   pushAt 1223 2 6144,
   pushAt 1224 2 1024,
   pushAt 1225 2 4137,
   opAt 1226 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1227 .JUMPDEST]

/-- Instructions 1265..1267, pc 1756..1760. The fixed-exponent candidate
redirects `BDONE` to its appended dispatcher; indices 1268..1271 are inert
padding and are not part of the executed block. -/
def blk1265 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1228 .JUMPDEST,
   pushAt 1229 2 3412,
   opAt 1230 .JUMP]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1231 .JUMPDEST,
   opAt 1232 (.Dup ⟨4, by decide⟩),
   opAt 1233 (.Dup ⟨1, by decide⟩),
   opAt 1234 .EQ,
   pushAt 1235 2 1776,
   opAt 1236 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1237 2 2343,
   opAt 1238 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1239 .JUMPDEST,
   pushAt 1240 2 1732,
   pushAt 1241 2 1024,
   pushAt 1242 2 1024,
   pushAt 1243 2 1024,
   pushAt 1244 2 4137,
   opAt 1245 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1246 .JUMPDEST,
   opAt 1247 (.Dup ⟨1, by decide⟩),
   opAt 1248 (.Dup ⟨1, by decide⟩),
   opAt 1249 .AND,
   opAt 1250 .ISZERO,
   pushAt 1251 2 1758,
   opAt 1252 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1253 2 1757,
   pushAt 1254 2 1024,
   pushAt 1255 2 2048,
   pushAt 1256 2 1024,
   pushAt 1257 2 4137,
   opAt 1258 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1259 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1260 .JUMPDEST,
   pushAt 1261 1 1,
   opAt 1262 .SHR,
   opAt 1263 (.Dup ⟨0, by decide⟩),
   pushAt 1264 2 1715,
   opAt 1265 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
