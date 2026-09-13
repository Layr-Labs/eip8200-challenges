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
  [opAt 1195 .POP,
   opAt 1196 .POP,
   pushAt 1197 1 1,
   opAt 1198 .ADD,
   pushAt 1199 2 1599,
   opAt 1200 .JUMP]

/-- Instructions 1402..1414, pc 1977..2002. -/
def blk1320 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1201 .JUMPDEST,
   opAt 1202 .POP,
   pushAt 1203 1 1,
   opAt 1204 (.Dup ⟨1, by decide⟩),
   pushAt 1205 2 736,
   opAt 1206 .ADD,
   opAt 1207 .MSTORE,
   pushAt 1208 2 1698,
   pushAt 1209 2 256,
   pushAt 1210 2 768,
   pushAt 1211 2 256,
   pushAt 1212 2 4092,
   opAt 1213 .JUMP]

/-- Instructions 1463..1470, pc 2003..2012. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1216 .JUMPDEST,
   opAt 1217 (.Dup ⟨4, by decide⟩),
   opAt 1218 (.Dup ⟨0, by decide⟩),
   opAt 1219 (.Dup ⟨2, by decide⟩),
   pushAt 1220 2 256,
   opAt 1221 .ADD,
   opAt 1222 .SUB,
   opAt 1223 .RETURN]

/-- Instructions 1471..1344, pc 2016..2016. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1224 .JUMPDEST,
   opAt 1225 .POP,
   pushAt 1226 2 1189,
   opAt 1227 .JUMP]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- Instructions 1481..1489, pc 1897..2037. -/
def blk1351 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1228 .JUMPDEST,
   opAt 1229 .POP,
   opAt 1230 .POP,
   opAt 1231 .POP,
   opAt 1232 .POP,
   opAt 1233 .POP,
   opAt 1234 .POP,
   pushAt 1235 2 1189,
   opAt 1236 .JUMP]

/-- Instructions 1408..1361, pc 2038..2039. -/
def blk1360 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1237 .JUMPDEST,
   pushAt 1238 2 256]

/-- Instructions 1362..1368, pc 2042..2052. -/
def blk1362 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1239 .JUMPDEST,
   pushAt 1240 2 1740,
   opAt 1241 (.Dup ⟨2, by decide⟩),
   opAt 1242 (.Dup ⟨0, by decide⟩),
   opAt 1243 (.Dup ⟨0, by decide⟩),
   pushAt 1244 2 2025,
   opAt 1245 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
