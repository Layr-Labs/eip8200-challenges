import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 6 (instructions 1396..1368). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1396..1323, pc 1971..1979. -/
def blk1314 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1203 .POP,
   opAt 1204 .POP,
   pushAt 1205 1 1,
   opAt 1206 .ADD,
   pushAt 1207 2 1604,
   opAt 1208 .JUMP]

/-- Instructions 1402..1414, pc 1980..2005. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1209 .JUMPDEST,
   opAt 1210 .POP,
   pushAt 1211 1 1,
   opAt 1212 (.Dup ⟨1, by decide⟩),
   pushAt 1213 2 736,
   opAt 1214 .ADD,
   opAt 1215 .MSTORE,
   pushAt 1216 2 1701,
   pushAt 1217 2 256,
   pushAt 1218 2 768,
   pushAt 1219 2 256,
   pushAt 1220 2 4151,
   opAt 1221 .JUMP]

/-- Instructions 1463..1470, pc 2006..2015. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1222 .JUMPDEST,
   opAt 1223 (.Dup ⟨4, by decide⟩),
   opAt 1224 (.Dup ⟨0, by decide⟩),
   opAt 1225 (.Dup ⟨2, by decide⟩),
   pushAt 1226 2 256,
   opAt 1227 .ADD,
   opAt 1228 .SUB,
   opAt 1229 .RETURN]

/-- Instructions 1471..1344, pc 2016..2021. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1230 .JUMPDEST,
   opAt 1231 .POP,
   pushAt 1232 2 1189,
   opAt 1233 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1481..1489, pc 1900..2040. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1234 .JUMPDEST,
   opAt 1235 .POP,
   opAt 1236 .POP,
   opAt 1237 .POP,
   opAt 1238 .POP,
   opAt 1239 .POP,
   opAt 1240 .POP,
   pushAt 1241 2 1189,
   opAt 1242 .JUMP]

/-- Instructions 1408..1361, pc 2041..2042. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1243 .JUMPDEST,
   pushAt 1244 2 256]

/-- Instructions 1362..1368, pc 2045..2055. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1245 .JUMPDEST,
   pushAt 1246 2 1743,
   opAt 1247 (.Dup ⟨2, by decide⟩),
   opAt 1248 (.Dup ⟨0, by decide⟩),
   opAt 1249 (.Dup ⟨0, by decide⟩),
   pushAt 1250 2 2028,
   opAt 1251 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
