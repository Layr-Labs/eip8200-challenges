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
  [opAt 1025 .JUMPDEST,
   opAt 1026 (.Dup ⟨0, by decide⟩),
   opAt 1027 .MLOAD,
   opAt 1028 (.Dup ⟨2, by decide⟩),
   opAt 1029 .MLOAD,
   opAt 1030 (.Dup ⟨1, by decide⟩),
   opAt 1031 (.Dup ⟨1, by decide⟩),
   opAt 1032 .GT,
   opAt 1033 (.Swap ⟨1, by decide⟩),
   opAt 1034 .SUB,
   opAt 1035 (.Dup ⟨5, by decide⟩),
   opAt 1036 (.Dup ⟨1, by decide⟩),
   opAt 1037 .SUB,
   opAt 1038 (.Swap ⟨0, by decide⟩),
   opAt 1039 (.Dup ⟨6, by decide⟩),
   opAt 1040 .GT,
   opAt 1041 (.Swap ⟨0, by decide⟩),
   opAt 1042 (.Swap ⟨1, by decide⟩),
   opAt 1043 .OR,
   opAt 1044 (.Swap ⟨4, by decide⟩),
   opAt 1045 .POP,
   opAt 1046 (.Dup ⟨3, by decide⟩),
   opAt 1047 .MSTORE,
   pushAt 1048 1 32,
   pushAt 1049 1 32,
   pushAt 1050 1 32,
   opAt 1051 (.Swap ⟨2, by decide⟩),
   opAt 1052 .SUB,
   opAt 1053 (.Swap ⟨2, by decide⟩),
   opAt 1054 .SUB,
   opAt 1055 (.Swap ⟨2, by decide⟩),
   opAt 1056 .SUB,
   opAt 1057 (.Swap ⟨1, by decide⟩),
   opAt 1058 (.Swap ⟨0, by decide⟩),
   opAt 1059 .JUMPDEST,
   opAt 1060 .JUMPDEST,
   pushAt 1061 2 2080,
   opAt 1062 (.Dup ⟨1, by decide⟩),
   opAt 1063 .GT,
   pushAt 1064 2 1443,
   opAt 1065 .JUMPI]

/-- Live instructions 1851..1866, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1066 .POP,
   opAt 1067 .POP,
   opAt 1068 .POP,
   opAt 1069 .ISZERO,
   pushAt 1070 2 2080,
   opAt 1071 .MLOAD,
   opAt 1072 .OR,
   pushAt 1073 2 319,
   opAt 1074 .NOT,
   opAt 1075 .MUL,
   pushAt 1076 2 2112,
   opAt 1077 .ADD,
   pushAt 1078 2 2688,
   opAt 1079 .MLOAD,
   opAt 1080 (.Swap ⟨1, by decide⟩),
   opAt 1081 .MCOPY,
   opAt 1082 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
