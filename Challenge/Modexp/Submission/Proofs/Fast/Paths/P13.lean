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
  [opAt 1024 .JUMPDEST,
   opAt 1025 (.Dup ⟨0, by decide⟩),
   opAt 1026 .MLOAD,
   opAt 1027 (.Dup ⟨2, by decide⟩),
   opAt 1028 .MLOAD,
   opAt 1029 (.Dup ⟨1, by decide⟩),
   opAt 1030 (.Dup ⟨1, by decide⟩),
   opAt 1031 .GT,
   opAt 1032 (.Swap ⟨1, by decide⟩),
   opAt 1033 .SUB,
   opAt 1034 (.Dup ⟨5, by decide⟩),
   opAt 1035 (.Dup ⟨1, by decide⟩),
   opAt 1036 .SUB,
   opAt 1037 (.Swap ⟨0, by decide⟩),
   opAt 1038 (.Dup ⟨6, by decide⟩),
   opAt 1039 .GT,
   opAt 1040 (.Swap ⟨0, by decide⟩),
   opAt 1041 (.Swap ⟨1, by decide⟩),
   opAt 1042 .OR,
   opAt 1043 (.Swap ⟨4, by decide⟩),
   opAt 1044 .POP,
   opAt 1045 (.Dup ⟨3, by decide⟩),
   opAt 1046 .MSTORE,
   pushAt 1047 1 31,
   opAt 1048 .NOT,
   opAt 1049 .ADD,
   opAt 1050 (.Swap ⟨0, by decide⟩),
   pushAt 1051 1 31,
   opAt 1052 .NOT,
   opAt 1053 .ADD,
   opAt 1054 (.Swap ⟨0, by decide⟩),
   opAt 1055 (.Swap ⟨1, by decide⟩),
   pushAt 1056 1 31,
   opAt 1057 .NOT,
   opAt 1058 .ADD,
   opAt 1059 (.Swap ⟨1, by decide⟩),
   pushAt 1060 2 2080,
   opAt 1061 (.Dup ⟨1, by decide⟩),
   opAt 1062 .GT,
   pushAt 1063 2 1443,
   opAt 1064 .JUMPI]

/-- Live instructions 1851..1866, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1065 .POP,
   opAt 1066 .POP,
   opAt 1067 .POP,
   opAt 1068 .ISZERO,
   pushAt 1069 2 2080,
   opAt 1070 .MLOAD,
   opAt 1071 .OR,
   pushAt 1072 2 319,
   opAt 1073 .NOT,
   opAt 1074 .MUL,
   pushAt 1075 2 2112,
   opAt 1076 .ADD,
   pushAt 1077 2 2688,
   opAt 1078 .MLOAD,
   opAt 1079 (.Swap ⟨1, by decide⟩),
   opAt 1080 .MCOPY,
   opAt 1081 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
