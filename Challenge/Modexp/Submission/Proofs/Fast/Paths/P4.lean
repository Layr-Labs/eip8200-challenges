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
  [pushAt 1041 2 2864,
   opAt 1042 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1043 .JUMPDEST,
   opAt 1044 (.Dup ⟨1, by decide⟩),
   opAt 1045 (.Dup ⟨1, by decide⟩),
   opAt 1046 .EQ,
   pushAt 1047 2 1446,
   opAt 1048 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1049 2 1403,
   pushAt 1050 2 1024,
   pushAt 1051 2 5120,
   pushAt 1052 2 1024,
   pushAt 1053 2 3900,
   opAt 1054 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1055 .JUMPDEST,
   opAt 1056 (.Dup ⟨0, by decide⟩),
   opAt 1057 (.Dup ⟨2, by decide⟩),
   opAt 1058 .SUB,
   pushAt 1059 1 5,
   opAt 1060 .SHL,
   opAt 1061 (.Dup ⟨5, by decide⟩),
   opAt 1062 .SUB,
   pushAt 1063 1 96,
   opAt 1064 .ADD,
   opAt 1065 .CALLDATALOAD,
   opAt 1066 (.Dup ⟨3, by decide⟩),
   pushAt 1067 2 3040,
   opAt 1068 .ADD,
   opAt 1069 .MSTORE,
   pushAt 1070 2 1438,
   pushAt 1071 2 1024,
   pushAt 1072 2 3072,
   pushAt 1073 2 1024,
   pushAt 1074 2 1894,
   opAt 1075 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1076 .JUMPDEST,
   pushAt 1077 1 1,
   opAt 1078 .ADD,
   pushAt 1079 2 1379,
   opAt 1080 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
