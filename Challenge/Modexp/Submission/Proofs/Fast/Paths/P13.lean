import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1824..1834). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1824..1864, pc 2410..2609. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1106 .JUMPDEST,
   opAt 1107 (.Dup ⟨0, by decide⟩),
   opAt 1108 .MLOAD,
   opAt 1109 (.Dup ⟨2, by decide⟩),
   opAt 1110 .MLOAD,
   opAt 1111 (.Dup ⟨1, by decide⟩),
   opAt 1112 (.Dup ⟨1, by decide⟩),
   opAt 1113 .GT,
   opAt 1114 (.Swap ⟨1, by decide⟩),
   opAt 1115 .SUB,
   opAt 1116 (.Dup ⟨5, by decide⟩),
   opAt 1117 (.Dup ⟨1, by decide⟩),
   opAt 1118 .SUB,
   opAt 1119 (.Swap ⟨0, by decide⟩),
   opAt 1120 (.Dup ⟨6, by decide⟩),
   opAt 1121 .GT,
   opAt 1122 (.Swap ⟨0, by decide⟩),
   opAt 1123 (.Swap ⟨1, by decide⟩),
   opAt 1124 .OR,
   opAt 1125 (.Swap ⟨4, by decide⟩),
   opAt 1126 .POP,
   opAt 1127 (.Dup ⟨3, by decide⟩),
   opAt 1128 .MSTORE,
   pushAt 1129 1 31,
   opAt 1130 .NOT,
   opAt 1131 .ADD,
   opAt 1132 (.Swap ⟨0, by decide⟩),
   pushAt 1133 1 31,
   opAt 1134 .NOT,
   opAt 1135 .ADD,
   opAt 1136 (.Swap ⟨0, by decide⟩),
   opAt 1137 (.Swap ⟨1, by decide⟩),
   pushAt 1138 1 31,
   opAt 1139 .NOT,
   opAt 1140 .ADD,
   opAt 1141 (.Swap ⟨1, by decide⟩),
   pushAt 1142 2 2080,
   opAt 1143 (.Dup ⟨1, by decide⟩),
   opAt 1144 .GT,
   pushAt 1145 2 1562,
   opAt 1146 .JUMPI]

/-- Live instructions 1865..1880, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1147 .POP,
   opAt 1148 .POP,
   opAt 1149 .POP,
   opAt 1150 .ISZERO,
   pushAt 1151 2 2080,
   opAt 1152 .MLOAD,
   opAt 1153 .OR,
   pushAt 1154 2 319,
   opAt 1155 .NOT,
   opAt 1156 .MUL,
   pushAt 1157 2 2112,
   opAt 1158 .ADD,
   pushAt 1159 2 2688,
   opAt 1160 .MLOAD,
   opAt 1161 (.Swap ⟨1, by decide⟩),
   opAt 1162 .MCOPY,
   opAt 1163 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
