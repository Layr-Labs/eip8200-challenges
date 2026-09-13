import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 4 (instructions 1325..1384). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1325..1326, pc 1766..1769: jump to the appended full-base
dispatcher. The remaining decoded instructions through index 1215 are
unreachable padding, preserving the old loop head at index 1216 / pc 1795. -/
def blk1195 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1112 2 3007,
   opAt 1113 .JUMP]

/-- Instructions 1216..1352, pc 1795..1803. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1114 .JUMPDEST,
   opAt 1115 (.Dup ⟨1, by decide⟩),
   opAt 1116 (.Dup ⟨1, by decide⟩),
   opAt 1117 .EQ,
   pushAt 1118 2 1580,
   opAt 1119 .JUMPI]

/-- Instructions 1353..1358, pc 1804..1819. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1120 2 1537,
   pushAt 1121 2 256,
   pushAt 1122 2 1280,
   pushAt 1123 2 256,
   pushAt 1124 2 4092,
   opAt 1125 .JUMP]

/-- Instructions 1359..1379, pc 1820..1806. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1126 .JUMPDEST,
   opAt 1127 (.Dup ⟨0, by decide⟩),
   opAt 1128 (.Dup ⟨2, by decide⟩),
   opAt 1129 .SUB,
   pushAt 1130 1 5,
   opAt 1131 .SHL,
   opAt 1132 (.Dup ⟨5, by decide⟩),
   opAt 1133 .SUB,
   pushAt 1134 1 96,
   opAt 1135 .ADD,
   opAt 1136 .CALLDATALOAD,
   opAt 1137 (.Dup ⟨3, by decide⟩),
   pushAt 1138 2 736,
   opAt 1139 .ADD,
   opAt 1140 .MSTORE,
   pushAt 1141 2 1572,
   pushAt 1142 2 256,
   pushAt 1143 2 768,
   pushAt 1144 2 256,
   pushAt 1145 2 2025,
   opAt 1146 .JUMP]

/-- Instructions 1332..1384, pc 1728..1814. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1147 .JUMPDEST,
   pushAt 1148 1 1,
   opAt 1149 .ADD,
   pushAt 1150 2 1513,
   opAt 1151 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
