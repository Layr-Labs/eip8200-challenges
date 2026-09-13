import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 6 (instructions 1396..1368). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1396..1323, pc 1968..1976. -/
def blk1314 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1200 .POP,
   opAt 1201 .POP,
   pushAt 1202 1 1,
   opAt 1203 .ADD,
   pushAt 1204 2 1599,
   opAt 1205 .JUMP]

/-- Instructions 1402..1414, pc 1977..2002. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1206 .JUMPDEST,
   opAt 1207 .POP,
   pushAt 1208 1 1,
   opAt 1209 (.Dup ⟨1, by decide⟩),
   pushAt 1210 2 736,
   opAt 1211 .ADD,
   opAt 1212 .MSTORE,
   pushAt 1213 2 1698,
   pushAt 1214 2 256,
   pushAt 1215 2 768,
   pushAt 1216 2 256,
   pushAt 1217 2 4086,
   opAt 1218 .JUMP]

/-- Instructions 1463..1470, pc 2003..2012. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1221 .JUMPDEST,
   opAt 1222 (.Dup ⟨4, by decide⟩),
   opAt 1223 (.Dup ⟨0, by decide⟩),
   opAt 1224 (.Dup ⟨2, by decide⟩),
   pushAt 1225 2 256,
   opAt 1226 .ADD,
   opAt 1227 .SUB,
   opAt 1228 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1229 .JUMPDEST,
   opAt 1230 .POP,
   pushAt 1231 2 1189,
   opAt 1232 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1481..1489, pc 1897..2037. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1233 .JUMPDEST,
   opAt 1234 .POP,
   opAt 1235 .POP,
   opAt 1236 .POP,
   opAt 1237 .POP,
   opAt 1238 .POP,
   opAt 1239 .POP,
   pushAt 1240 2 1189,
   opAt 1241 .JUMP]

/-- Instructions 1408..1361, pc 2038..2039. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1242 .JUMPDEST,
   pushAt 1243 2 256]

/-- Instructions 1362..1368, pc 2042..2052. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1244 .JUMPDEST,
   pushAt 1245 2 1740,
   opAt 1246 (.Dup ⟨2, by decide⟩),
   opAt 1247 (.Dup ⟨0, by decide⟩),
   opAt 1248 (.Dup ⟨0, by decide⟩),
   pushAt 1249 2 2025,
   opAt 1250 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
