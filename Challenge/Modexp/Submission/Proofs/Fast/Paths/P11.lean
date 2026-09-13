import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (instructions 1569..1753). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1569..1721, pc 2304..2592. -/
def blk1569 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1011 .POP,
   opAt 1012 .POP,
   opAt 1013 (.Swap ⟨1, by decide⟩),
   opAt 1014 .POP,
   opAt 1015 .POP,
   opAt 1016 (.Dup ⟨0, by decide⟩),
   pushAt 1017 2 2080,
   opAt 1018 .MLOAD,
   opAt 1019 .ADD,
   opAt 1020 (.Dup ⟨0, by decide⟩),
   pushAt 1021 2 2112,
   opAt 1022 .MSTORE,
   opAt 1023 .LT,
   pushAt 1024 2 2048,
   opAt 1025 .MLOAD,
   opAt 1026 .ADD,
   pushAt 1027 2 2080,
   opAt 1028 .MSTORE,
   pushAt 1029 1 31,
   opAt 1030 .NOT,
   opAt 1031 .ADD,
   opAt 1032 (.Dup ⟨2, by decide⟩),
   opAt 1033 (.Dup ⟨1, by decide⟩),
   opAt 1034 .GT,
   pushAt 1035 2 1254,
   opAt 1036 .JUMPI]

/-- Instructions 1672..1726, pc 2595..2346. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1037 .POP,
   opAt 1038 .POP,
   opAt 1039 .POP,
   pushAt 1040 2 4337,
   opAt 1041 .JUMP]

/-- Instructions 1600..1753, pc 2347..2379. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1042 .JUMPDEST,
   pushAt 1043 2 2688,
   opAt 1044 .MLOAD,
   opAt 1045 (.Dup ⟨0, by decide⟩),
   opAt 1046 (.Dup ⟨2, by decide⟩),
   opAt 1047 .ADD,
   pushAt 1048 1 32,
   opAt 1049 (.Swap ⟨0, by decide⟩),
   opAt 1050 .SUB,
   opAt 1051 (.Dup ⟨1, by decide⟩),
   opAt 1052 (.Dup ⟨4, by decide⟩),
   opAt 1053 .ADD,
   pushAt 1054 1 32,
   opAt 1055 (.Swap ⟨0, by decide⟩),
   opAt 1056 .SUB,
   opAt 1057 (.Swap ⟨2, by decide⟩),
   opAt 1058 .POP,
   opAt 1059 (.Swap ⟨2, by decide⟩),
   opAt 1060 .POP,
   opAt 1061 .POP,
   pushAt 1062 2 2784,
   opAt 1063 .MLOAD,
   pushAt 1064 0 0,
   opAt 1065 (.Swap ⟨2, by decide⟩),
   opAt 1066 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
