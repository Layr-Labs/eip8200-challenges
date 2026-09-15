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
  [opAt 1023 .JUMPDEST,
   opAt 1024 (.Dup ⟨0, by decide⟩),
   opAt 1025 .MLOAD,
   opAt 1026 (.Dup ⟨2, by decide⟩),
   opAt 1027 .MLOAD,
   opAt 1028 (.Dup ⟨1, by decide⟩),
   opAt 1029 (.Dup ⟨1, by decide⟩),
   opAt 1030 .GT,
   opAt 1031 (.Swap ⟨1, by decide⟩),
   opAt 1032 .SUB,
   opAt 1033 (.Dup ⟨5, by decide⟩),
   opAt 1034 (.Dup ⟨1, by decide⟩),
   opAt 1035 .SUB,
   opAt 1036 (.Swap ⟨0, by decide⟩),
   opAt 1037 (.Dup ⟨6, by decide⟩),
   opAt 1038 .GT,
   opAt 1039 (.Swap ⟨0, by decide⟩),
   opAt 1040 (.Swap ⟨1, by decide⟩),
   opAt 1041 .OR,
   opAt 1042 (.Swap ⟨4, by decide⟩),
   opAt 1043 .POP,
   opAt 1044 (.Dup ⟨3, by decide⟩),
   opAt 1045 .MSTORE,
   pushAt 1046 1 31,
   opAt 1047 .NOT,
   opAt 1048 .ADD,
   opAt 1049 (.Swap ⟨0, by decide⟩),
   pushAt 1050 1 31,
   opAt 1051 .NOT,
   opAt 1052 .ADD,
   opAt 1053 (.Swap ⟨0, by decide⟩),
   opAt 1054 (.Swap ⟨1, by decide⟩),
   pushAt 1055 1 31,
   opAt 1056 .NOT,
   opAt 1057 .ADD,
   opAt 1058 (.Swap ⟨1, by decide⟩),
   pushAt 1059 2 2080,
   opAt 1060 (.Dup ⟨1, by decide⟩),
   opAt 1061 .GT,
   pushAt 1062 2 1443,
   opAt 1063 .JUMPI]

/-- Live instructions 1851..1866, pc 2848..2995; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1064 .POP,
   opAt 1065 .POP,
   opAt 1066 .POP,
   opAt 1067 .ISZERO,
   pushAt 1068 2 2080,
   opAt 1069 .MLOAD,
   opAt 1070 .OR,
   pushAt 1071 2 319,
   opAt 1072 .NOT,
   opAt 1073 .MUL,
   pushAt 1074 2 2112,
   opAt 1075 .ADD,
   pushAt 1076 2 2688,
   opAt 1077 .MLOAD,
   opAt 1078 (.Swap ⟨1, by decide⟩),
   opAt 1079 .MCOPY,
   opAt 1080 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
