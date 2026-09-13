import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1810..1820). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1810..1850, pc 2411..2608. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1112 .JUMPDEST,
   opAt 1113 (.Dup ⟨0, by decide⟩),
   opAt 1114 .MLOAD,
   opAt 1115 (.Dup ⟨2, by decide⟩),
   opAt 1116 .MLOAD,
   opAt 1117 (.Dup ⟨1, by decide⟩),
   opAt 1118 (.Dup ⟨1, by decide⟩),
   opAt 1119 .GT,
   opAt 1120 (.Swap ⟨1, by decide⟩),
   opAt 1121 .SUB,
   opAt 1122 (.Dup ⟨5, by decide⟩),
   opAt 1123 (.Dup ⟨1, by decide⟩),
   opAt 1124 .SUB,
   opAt 1125 (.Swap ⟨0, by decide⟩),
   opAt 1126 (.Dup ⟨6, by decide⟩),
   opAt 1127 .GT,
   opAt 1128 (.Swap ⟨0, by decide⟩),
   opAt 1129 (.Swap ⟨1, by decide⟩),
   opAt 1130 .OR,
   opAt 1131 (.Swap ⟨4, by decide⟩),
   opAt 1132 .POP,
   opAt 1133 (.Dup ⟨3, by decide⟩),
   opAt 1134 .MSTORE,
   pushAt 1135 1 31,
   opAt 1136 .NOT,
   opAt 1137 .ADD,
   opAt 1138 (.Swap ⟨0, by decide⟩),
   pushAt 1139 1 31,
   opAt 1140 .NOT,
   opAt 1141 .ADD,
   opAt 1142 (.Swap ⟨0, by decide⟩),
   opAt 1143 (.Swap ⟨1, by decide⟩),
   pushAt 1144 1 31,
   opAt 1145 .NOT,
   opAt 1146 .ADD,
   opAt 1147 (.Swap ⟨1, by decide⟩),
   pushAt 1148 2 2080,
   opAt 1149 (.Dup ⟨1, by decide⟩),
   opAt 1150 .GT,
   pushAt 1151 2 1578,
   opAt 1152 .JUMPI]

/-- Live instructions 1851..1866, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1153 .POP,
   opAt 1154 .POP,
   opAt 1155 .POP,
   opAt 1156 .ISZERO,
   pushAt 1157 2 2080,
   opAt 1158 .MLOAD,
   opAt 1159 .OR,
   pushAt 1160 2 319,
   opAt 1161 .NOT,
   opAt 1162 .MUL,
   pushAt 1163 2 2112,
   opAt 1164 .ADD,
   pushAt 1165 2 2688,
   opAt 1166 .MLOAD,
   opAt 1167 (.Swap ⟨1, by decide⟩),
   opAt 1168 .MCOPY,
   opAt 1169 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
