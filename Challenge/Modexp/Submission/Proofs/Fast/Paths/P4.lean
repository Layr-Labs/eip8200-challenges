import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 4 (instructions 1325..1384). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1325..1326, pc 1769..1772: jump to the appended full-base
dispatcher. The remaining decoded instructions through index 1215 are
unreachable padding, preserving the old loop head at index 1216 / pc 1798. -/
def blk1195 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1116 2 2995,
   opAt 1117 .JUMP]

/-- Instructions 1216..1352, pc 1798..1806. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1118 .JUMPDEST,
   opAt 1119 (.Dup ⟨1, by decide⟩),
   opAt 1120 (.Dup ⟨1, by decide⟩),
   opAt 1121 .EQ,
   pushAt 1122 2 1580,
   opAt 1123 .JUMPI]

/-- Instructions 1353..1358, pc 1807..1822. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1124 2 1537,
   pushAt 1125 2 256,
   pushAt 1126 2 1280,
   pushAt 1127 2 256,
   pushAt 1128 2 4137,
   opAt 1129 .JUMP]

/-- Instructions 1359..1379, pc 1823..1809. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1130 .JUMPDEST,
   opAt 1131 (.Dup ⟨0, by decide⟩),
   opAt 1132 (.Dup ⟨2, by decide⟩),
   opAt 1133 .SUB,
   pushAt 1134 1 5,
   opAt 1135 .SHL,
   opAt 1136 (.Dup ⟨5, by decide⟩),
   opAt 1137 .SUB,
   pushAt 1138 1 96,
   opAt 1139 .ADD,
   opAt 1140 .CALLDATALOAD,
   opAt 1141 (.Dup ⟨3, by decide⟩),
   pushAt 1142 2 736,
   opAt 1143 .ADD,
   opAt 1144 .MSTORE,
   pushAt 1145 2 1572,
   pushAt 1146 2 256,
   pushAt 1147 2 768,
   pushAt 1148 2 256,
   pushAt 1149 2 2028,
   opAt 1150 .JUMP]

/-- Instructions 1332..1384, pc 1728..1817. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1151 .JUMPDEST,
   pushAt 1152 1 1,
   opAt 1153 .ADD,
   pushAt 1154 2 1513,
   opAt 1155 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
