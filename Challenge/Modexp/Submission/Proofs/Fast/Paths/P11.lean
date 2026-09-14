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
  [opAt 1005 .POP,
   opAt 1006 .POP,
   opAt 1007 (.Swap ⟨1, by decide⟩),
   opAt 1008 .POP,
   opAt 1009 .POP,
   opAt 1010 (.Dup ⟨0, by decide⟩),
   pushAt 1011 2 2080,
   opAt 1012 .MLOAD,
   opAt 1013 .ADD,
   opAt 1014 (.Dup ⟨0, by decide⟩),
   pushAt 1015 2 2112,
   opAt 1016 .MSTORE,
   opAt 1017 .LT,
   pushAt 1018 2 2048,
   opAt 1019 .MLOAD,
   opAt 1020 .ADD,
   pushAt 1021 2 2080,
   opAt 1022 .MSTORE,
   pushAt 1023 1 31,
   opAt 1024 .NOT,
   opAt 1025 .ADD,
   opAt 1026 (.Dup ⟨2, by decide⟩),
   opAt 1027 (.Dup ⟨1, by decide⟩),
   opAt 1028 .GT,
   pushAt 1029 2 1238,
   opAt 1030 .JUMPI]

/-- Instructions 1672..1726, pc 2595..2346. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1031 .POP,
   opAt 1032 .POP,
   opAt 1033 .POP,
   pushAt 1034 2 4330,
   opAt 1035 .JUMP]

/-- Instructions 1600..1753, pc 2347..2379. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1036 .JUMPDEST,
   pushAt 1037 2 2688,
   opAt 1038 .MLOAD,
   opAt 1039 (.Dup ⟨0, by decide⟩),
   opAt 1040 (.Dup ⟨2, by decide⟩),
   opAt 1041 .ADD,
   pushAt 1042 1 32,
   opAt 1043 (.Swap ⟨0, by decide⟩),
   opAt 1044 .SUB,
   opAt 1045 (.Dup ⟨1, by decide⟩),
   opAt 1046 (.Dup ⟨4, by decide⟩),
   opAt 1047 .ADD,
   pushAt 1048 1 32,
   opAt 1049 (.Swap ⟨0, by decide⟩),
   opAt 1050 .SUB,
   opAt 1051 (.Swap ⟨2, by decide⟩),
   opAt 1052 .POP,
   opAt 1053 (.Swap ⟨2, by decide⟩),
   opAt 1054 .POP,
   opAt 1055 .POP,
   pushAt 1056 2 2784,
   opAt 1057 .MLOAD,
   pushAt 1058 0 0,
   opAt 1059 (.Swap ⟨2, by decide⟩),
   opAt 1060 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
