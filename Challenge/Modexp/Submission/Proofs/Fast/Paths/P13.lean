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
  [opAt 1105 .JUMPDEST,
   opAt 1106 (.Dup ⟨0, by decide⟩),
   opAt 1107 .MLOAD,
   opAt 1108 (.Dup ⟨2, by decide⟩),
   opAt 1109 .MLOAD,
   opAt 1110 (.Dup ⟨1, by decide⟩),
   opAt 1111 (.Dup ⟨1, by decide⟩),
   opAt 1112 .GT,
   opAt 1113 (.Swap ⟨1, by decide⟩),
   opAt 1114 .SUB,
   opAt 1115 (.Dup ⟨5, by decide⟩),
   opAt 1116 (.Dup ⟨1, by decide⟩),
   opAt 1117 .SUB,
   opAt 1118 (.Swap ⟨0, by decide⟩),
   opAt 1119 (.Dup ⟨6, by decide⟩),
   opAt 1120 .GT,
   opAt 1121 (.Swap ⟨0, by decide⟩),
   opAt 1122 (.Swap ⟨1, by decide⟩),
   opAt 1123 .OR,
   opAt 1124 (.Swap ⟨4, by decide⟩),
   opAt 1125 .POP,
   opAt 1126 (.Dup ⟨3, by decide⟩),
   opAt 1127 .MSTORE,
   pushAt 1128 1 31,
   opAt 1129 .NOT,
   opAt 1130 .ADD,
   opAt 1131 (.Swap ⟨0, by decide⟩),
   pushAt 1132 1 31,
   opAt 1133 .NOT,
   opAt 1134 .ADD,
   opAt 1135 (.Swap ⟨0, by decide⟩),
   opAt 1136 (.Swap ⟨1, by decide⟩),
   pushAt 1137 1 31,
   opAt 1138 .NOT,
   opAt 1139 .ADD,
   opAt 1140 (.Swap ⟨1, by decide⟩),
   pushAt 1141 2 2080,
   opAt 1142 (.Dup ⟨1, by decide⟩),
   opAt 1143 .GT,
   pushAt 1144 2 1562,
   opAt 1145 .JUMPI]

/-- Live instructions 1851..1866, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1146 .POP,
   opAt 1147 .POP,
   opAt 1148 .POP,
   opAt 1149 .ISZERO,
   pushAt 1150 2 2080,
   opAt 1151 .MLOAD,
   opAt 1152 .OR,
   pushAt 1153 2 319,
   opAt 1154 .NOT,
   opAt 1155 .MUL,
   pushAt 1156 2 2112,
   opAt 1157 .ADD,
   pushAt 1158 2 2688,
   opAt 1159 .MLOAD,
   opAt 1160 (.Swap ⟨1, by decide⟩),
   opAt 1161 .MCOPY,
   opAt 1162 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
