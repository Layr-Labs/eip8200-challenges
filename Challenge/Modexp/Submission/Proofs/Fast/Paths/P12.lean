import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1755..1823). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1755..1796, pc 2379..2764. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1061 .JUMPDEST,
   opAt 1062 (.Dup ⟨1, by decide⟩),
   opAt 1063 .MLOAD,
   opAt 1064 (.Dup ⟨3, by decide⟩),
   opAt 1065 .MLOAD,
   opAt 1066 (.Dup ⟨1, by decide⟩),
   opAt 1067 .ADD,
   opAt 1068 (.Swap ⟨0, by decide⟩),
   opAt 1069 (.Dup ⟨1, by decide⟩),
   opAt 1070 .LT,
   opAt 1071 (.Swap ⟨0, by decide⟩),
   opAt 1072 (.Dup ⟨5, by decide⟩),
   opAt 1073 .ADD,
   opAt 1074 (.Swap ⟨4, by decide⟩),
   opAt 1075 (.Dup ⟨5, by decide⟩),
   opAt 1076 .LT,
   opAt 1077 .OR,
   opAt 1078 (.Swap ⟨3, by decide⟩),
   opAt 1079 (.Dup ⟨1, by decide⟩),
   opAt 1080 .MSTORE,
   pushAt 1081 1 31,
   opAt 1082 .NOT,
   opAt 1083 .ADD,
   opAt 1084 (.Swap ⟨0, by decide⟩),
   pushAt 1085 1 31,
   opAt 1086 .NOT,
   opAt 1087 .ADD,
   opAt 1088 (.Swap ⟨0, by decide⟩),
   opAt 1089 (.Swap ⟨1, by decide⟩),
   pushAt 1090 1 31,
   opAt 1091 .NOT,
   opAt 1092 .ADD,
   opAt 1093 (.Swap ⟨1, by decide⟩),
   pushAt 1094 2 2080,
   opAt 1095 (.Dup ⟨1, by decide⟩),
   opAt 1096 .GT,
   pushAt 1097 2 1506,
   opAt 1098 .JUMPI]

/-- Instructions 1792..1745, pc 2765..2430. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1099 .POP,
   opAt 1100 .POP,
   opAt 1101 .POP,
   pushAt 1102 2 2080,
   opAt 1103 .MSTORE,
   pushAt 1104 2 4320,
   opAt 1105 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
