import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1809..1819). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1809..1849, pc 2410..2609. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1104 .JUMPDEST,
   opAt 1105 (.Dup ⟨0, by decide⟩),
   opAt 1106 .MLOAD,
   opAt 1107 (.Dup ⟨2, by decide⟩),
   opAt 1108 .MLOAD,
   opAt 1109 (.Dup ⟨1, by decide⟩),
   opAt 1110 (.Dup ⟨1, by decide⟩),
   opAt 1111 .GT,
   opAt 1112 (.Swap ⟨1, by decide⟩),
   opAt 1113 .SUB,
   opAt 1114 (.Dup ⟨5, by decide⟩),
   opAt 1115 (.Dup ⟨1, by decide⟩),
   opAt 1116 .SUB,
   opAt 1117 (.Swap ⟨0, by decide⟩),
   opAt 1118 (.Dup ⟨6, by decide⟩),
   opAt 1119 .GT,
   opAt 1120 (.Swap ⟨0, by decide⟩),
   opAt 1121 (.Swap ⟨1, by decide⟩),
   opAt 1122 .OR,
   opAt 1123 (.Swap ⟨4, by decide⟩),
   opAt 1124 .POP,
   opAt 1125 (.Dup ⟨3, by decide⟩),
   opAt 1126 .MSTORE,
   pushAt 1127 1 31,
   opAt 1128 .NOT,
   opAt 1129 .ADD,
   opAt 1130 (.Swap ⟨0, by decide⟩),
   pushAt 1131 1 31,
   opAt 1132 .NOT,
   opAt 1133 .ADD,
   opAt 1134 (.Swap ⟨0, by decide⟩),
   opAt 1135 (.Swap ⟨1, by decide⟩),
   pushAt 1136 1 31,
   opAt 1137 .NOT,
   opAt 1138 .ADD,
   opAt 1139 (.Swap ⟨1, by decide⟩),
   pushAt 1140 2 2080,
   opAt 1141 (.Dup ⟨1, by decide⟩),
   opAt 1142 .GT,
   pushAt 1143 2 1561,
   opAt 1144 .JUMPI]

/-- Live instructions 1850..1865, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1145 .POP,
   opAt 1146 .POP,
   opAt 1147 .POP,
   opAt 1148 .ISZERO,
   pushAt 1149 2 2080,
   opAt 1150 .MLOAD,
   opAt 1151 .OR,
   pushAt 1152 2 319,
   opAt 1153 .NOT,
   opAt 1154 .MUL,
   pushAt 1155 2 2112,
   opAt 1156 .ADD,
   pushAt 1157 2 2688,
   opAt 1158 .MLOAD,
   opAt 1159 (.Swap ⟨1, by decide⟩),
   opAt 1160 .MCOPY,
   opAt 1161 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
