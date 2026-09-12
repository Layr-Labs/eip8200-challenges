import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1369..1420). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1369..1375, pc 1926..1935. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1075 .JUMPDEST,
   pushAt 1076 1 1,
   opAt 1077 (.Swap ⟨0, by decide⟩),
   opAt 1078 .SUB,
   opAt 1079 (.Dup ⟨0, by decide⟩),
   pushAt 1080 2 1469,
   opAt 1081 .JUMPI]

/-- Instructions 1376..1378, pc 1936..1938. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1082 .POP,
   opAt 1083 .POP,
   opAt 1084 .JUMP]

/-- Instructions 1379..1405, pc 1939..1973. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1085 .JUMPDEST,
   pushAt 1086 2 9344,
   opAt 1087 .MLOAD,
   opAt 1088 (.Dup ⟨0, by decide⟩),
   pushAt 1089 1 64,
   opAt 1090 .ADD,
   opAt 1091 .CALLDATASIZE,
   pushAt 1092 2 8192,
   opAt 1093 .CALLDATACOPY,
   opAt 1094 (.Dup ⟨0, by decide⟩),
   opAt 1095 (.Dup ⟨3, by decide⟩),
   opAt 1096 .ADD,
   pushAt 1097 1 32,
   opAt 1098 (.Swap ⟨0, by decide⟩),
   opAt 1099 .SUB,
   pushAt 1100 1 32,
   opAt 1101 (.Dup ⟨4, by decide⟩),
   opAt 1102 .SUB,
   opAt 1103 (.Swap ⟨3, by decide⟩),
   opAt 1104 .POP,
   opAt 1105 (.Swap ⟨0, by decide⟩),
   opAt 1106 .POP,
   pushAt 1107 1 32,
   opAt 1108 (.Dup ⟨2, by decide⟩),
   opAt 1109 .SUB,
   opAt 1110 (.Swap ⟨1, by decide⟩),
   opAt 1111 .POP]

/-- Instructions 1406..1420, pc 1974..1994. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1112 .JUMPDEST,
   opAt 1113 (.Dup ⟨0, by decide⟩),
   opAt 1114 .MLOAD,
   pushAt 1115 0 0,
   pushAt 1116 2 9440,
   opAt 1117 .MLOAD,
   opAt 1118 (.Dup ⟨4, by decide⟩),
   pushAt 1119 2 9344,
   opAt 1120 .MLOAD,
   opAt 1121 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
