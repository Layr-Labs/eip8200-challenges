import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 4 (instructions 1195..1254). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1195..1196, pc 1639..1642: jump to the appended full-base
dispatcher. The remaining decoded instructions through index 1215 are
unreachable padding, preserving the old loop head at index 1216 / pc 1668. -/
def blk1195 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1179 2 3333,
   opAt 1180 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1200 .JUMPDEST,
   opAt 1201 (.Dup ⟨1, by decide⟩),
   opAt 1202 (.Dup ⟨1, by decide⟩),
   opAt 1203 .EQ,
   pushAt 1204 2 1718,
   opAt 1205 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1206 2 1675,
   pushAt 1207 2 1024,
   pushAt 1208 2 5120,
   pushAt 1209 2 1024,
   pushAt 1210 2 4428,
   opAt 1211 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1212 .JUMPDEST,
   opAt 1213 (.Dup ⟨0, by decide⟩),
   opAt 1214 (.Dup ⟨2, by decide⟩),
   opAt 1215 .SUB,
   pushAt 1216 1 5,
   opAt 1217 .SHL,
   opAt 1218 (.Dup ⟨5, by decide⟩),
   opAt 1219 .SUB,
   pushAt 1220 1 96,
   opAt 1221 .ADD,
   opAt 1222 .CALLDATALOAD,
   opAt 1223 (.Dup ⟨3, by decide⟩),
   pushAt 1224 2 3040,
   opAt 1225 .ADD,
   opAt 1226 .MSTORE,
   pushAt 1227 2 1710,
   pushAt 1228 2 1024,
   pushAt 1229 2 3072,
   pushAt 1230 2 1024,
   pushAt 1231 2 2199,
   opAt 1232 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1233 .JUMPDEST,
   pushAt 1234 1 1,
   opAt 1235 .ADD,
   pushAt 1236 2 1651,
   opAt 1237 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
