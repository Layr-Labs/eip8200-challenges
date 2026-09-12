import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1421..1468). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1421..1468, pc 1995..2049. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1122 .JUMPDEST,
   opAt 1123 (.Dup ⟨3, by decide⟩),
   opAt 1124 (.Dup ⟨1, by decide⟩),
   opAt 1125 .MLOAD,
   opAt 1126 (.Dup ⟨1, by decide⟩),
   opAt 1127 (.Dup ⟨1, by decide⟩),
   opAt 1128 .MUL,
   opAt 1129 (.Swap ⟨1, by decide⟩),
   pushAt 1130 0 0,
   opAt 1131 .NOT,
   opAt 1132 (.Swap ⟨1, by decide⟩),
   opAt 1133 .MULMOD,
   opAt 1134 (.Dup ⟨1, by decide⟩),
   opAt 1135 (.Dup ⟨1, by decide⟩),
   opAt 1136 .LT,
   opAt 1137 (.Dup ⟨2, by decide⟩),
   opAt 1138 .ADD,
   opAt 1139 (.Swap ⟨0, by decide⟩),
   opAt 1140 .SUB,
   opAt 1141 (.Dup ⟨3, by decide⟩),
   opAt 1142 .MLOAD,
   opAt 1143 (.Swap ⟨1, by decide⟩),
   opAt 1144 (.Dup ⟨2, by decide⟩),
   opAt 1145 .ADD,
   opAt 1146 (.Swap ⟨1, by decide⟩),
   opAt 1147 (.Dup ⟨2, by decide⟩),
   opAt 1148 .LT,
   opAt 1149 .ADD,
   opAt 1150 (.Swap ⟨0, by decide⟩),
   opAt 1151 (.Dup ⟨4, by decide⟩),
   opAt 1152 .ADD,
   opAt 1153 (.Swap ⟨3, by decide⟩),
   opAt 1154 (.Dup ⟨4, by decide⟩),
   opAt 1155 .LT,
   opAt 1156 .ADD,
   opAt 1157 (.Swap ⟨2, by decide⟩),
   opAt 1158 (.Dup ⟨2, by decide⟩),
   opAt 1159 .MSTORE,
   pushAt 1160 1 31,
   opAt 1161 .NOT,
   opAt 1162 .ADD,
   opAt 1163 (.Swap ⟨0, by decide⟩),
   pushAt 1164 1 31,
   opAt 1165 .NOT,
   opAt 1166 .ADD,
   opAt 1167 (.Swap ⟨0, by decide⟩),
   opAt 1168 (.Dup ⟨5, by decide⟩),
   opAt 1169 (.Dup ⟨1, by decide⟩),
   opAt 1170 .GT,
   pushAt 1171 2 1542,
   opAt 1172 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
