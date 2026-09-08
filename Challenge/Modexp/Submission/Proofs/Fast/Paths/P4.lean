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
  [pushAt 1188 2 3345,
   opAt 1189 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1209 .JUMPDEST,
   opAt 1210 (.Dup ⟨1, by decide⟩),
   opAt 1211 (.Dup ⟨1, by decide⟩),
   opAt 1212 .EQ,
      pushAt 1213 2 1728,
   opAt 1214 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1215 2 1685,
   pushAt 1216 2 1024,
   pushAt 1217 2 5120,
   pushAt 1218 2 1024,
   pushAt 1219 2 4432,
   opAt 1220 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1221 .JUMPDEST,
   opAt 1222 (.Dup ⟨0, by decide⟩),
   opAt 1223 (.Dup ⟨2, by decide⟩),
   opAt 1224 .SUB,
   pushAt 1225 1 5,
   opAt 1226 .SHL,
   opAt 1227 (.Dup ⟨5, by decide⟩),
   opAt 1228 .SUB,
   pushAt 1229 1 96,
   opAt 1230 .ADD,
   opAt 1231 .CALLDATALOAD,
   opAt 1232 (.Dup ⟨3, by decide⟩),
   pushAt 1233 2 3040,
   opAt 1234 .ADD,
   opAt 1235 .MSTORE,
   pushAt 1236 2 1720,
   pushAt 1237 2 1024,
   pushAt 1238 2 3072,
   pushAt 1239 2 1024,
   pushAt 1240 2 2209,
   opAt 1241 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1242 .JUMPDEST,
   pushAt 1243 1 1,
   opAt 1244 .ADD,
   pushAt 1245 2 1661,
   opAt 1246 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
