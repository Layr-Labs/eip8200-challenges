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
  [pushAt 1043 2 2868,
   opAt 1044 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1045 .JUMPDEST,
   opAt 1046 (.Dup ⟨1, by decide⟩),
   opAt 1047 (.Dup ⟨1, by decide⟩),
   opAt 1048 .EQ,
   pushAt 1049 2 1450,
   opAt 1050 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1051 2 1407,
   pushAt 1052 2 1024,
   pushAt 1053 2 5120,
   pushAt 1054 2 1024,
   pushAt 1055 2 3873,
   opAt 1056 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1057 .JUMPDEST,
   opAt 1058 (.Dup ⟨0, by decide⟩),
   opAt 1059 (.Dup ⟨2, by decide⟩),
   opAt 1060 .SUB,
   pushAt 1061 1 5,
   opAt 1062 .SHL,
   opAt 1063 (.Dup ⟨5, by decide⟩),
   opAt 1064 .SUB,
   pushAt 1065 1 96,
   opAt 1066 .ADD,
   opAt 1067 .CALLDATALOAD,
   opAt 1068 (.Dup ⟨3, by decide⟩),
   pushAt 1069 2 3040,
   opAt 1070 .ADD,
   opAt 1071 .MSTORE,
   pushAt 1072 2 1442,
   pushAt 1073 2 1024,
   pushAt 1074 2 3072,
   pushAt 1075 2 1024,
   pushAt 1076 2 1898,
   opAt 1077 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1078 .JUMPDEST,
   pushAt 1079 1 1,
   opAt 1080 .ADD,
   pushAt 1081 2 1383,
   opAt 1082 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
