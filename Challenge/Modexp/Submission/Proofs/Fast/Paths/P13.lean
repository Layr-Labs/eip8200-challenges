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
  [opAt 1107 .JUMPDEST,
   opAt 1108 (.Dup ⟨0, by decide⟩),
   opAt 1109 .MLOAD,
   opAt 1110 (.Dup ⟨2, by decide⟩),
   opAt 1111 .MLOAD,
   opAt 1112 (.Dup ⟨1, by decide⟩),
   opAt 1113 (.Dup ⟨1, by decide⟩),
   opAt 1114 .GT,
   opAt 1115 (.Swap ⟨1, by decide⟩),
   opAt 1116 .SUB,
   opAt 1117 (.Dup ⟨5, by decide⟩),
   opAt 1118 (.Dup ⟨1, by decide⟩),
   opAt 1119 .SUB,
   opAt 1120 (.Swap ⟨0, by decide⟩),
   opAt 1121 (.Dup ⟨6, by decide⟩),
   opAt 1122 .GT,
   opAt 1123 (.Swap ⟨0, by decide⟩),
   opAt 1124 (.Swap ⟨1, by decide⟩),
   opAt 1125 .OR,
   opAt 1126 (.Swap ⟨4, by decide⟩),
   opAt 1127 .POP,
   opAt 1128 (.Dup ⟨3, by decide⟩),
   opAt 1129 .MSTORE,
   pushAt 1130 1 31,
   opAt 1131 .NOT,
   opAt 1132 .ADD,
   opAt 1133 (.Swap ⟨0, by decide⟩),
   pushAt 1134 1 31,
   opAt 1135 .NOT,
   opAt 1136 .ADD,
   opAt 1137 (.Swap ⟨0, by decide⟩),
   opAt 1138 (.Swap ⟨1, by decide⟩),
   pushAt 1139 1 31,
   opAt 1140 .NOT,
   opAt 1141 .ADD,
   opAt 1142 (.Swap ⟨1, by decide⟩),
   pushAt 1143 2 2080,
   opAt 1144 (.Dup ⟨1, by decide⟩),
   opAt 1145 .GT,
   pushAt 1146 2 1578,
   opAt 1147 .JUMPI]

/-- Live instructions 1851..1866, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1148 .POP,
   opAt 1149 .POP,
   opAt 1150 .POP,
   opAt 1151 .ISZERO,
   pushAt 1152 2 2080,
   opAt 1153 .MLOAD,
   opAt 1154 .OR,
   pushAt 1155 2 319,
   opAt 1156 .NOT,
   opAt 1157 .MUL,
   pushAt 1158 2 2112,
   opAt 1159 .ADD,
   pushAt 1160 2 2688,
   opAt 1161 .MLOAD,
   opAt 1162 (.Swap ⟨1, by decide⟩),
   opAt 1163 .MCOPY,
   opAt 1164 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
