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
  [opAt 1004 .POP,
   opAt 1005 .POP,
   opAt 1006 (.Swap ⟨1, by decide⟩),
   opAt 1007 .POP,
   opAt 1008 .POP,
   opAt 1009 (.Dup ⟨0, by decide⟩),
   pushAt 1010 2 2080,
   opAt 1011 .MLOAD,
   opAt 1012 .ADD,
   opAt 1013 (.Dup ⟨0, by decide⟩),
   pushAt 1014 2 2112,
   opAt 1015 .MSTORE,
   opAt 1016 .LT,
   pushAt 1017 2 2048,
   opAt 1018 .MLOAD,
   opAt 1019 .ADD,
   pushAt 1020 2 2080,
   opAt 1021 .MSTORE,
   pushAt 1022 1 31,
   opAt 1023 .NOT,
   opAt 1024 .ADD,
   opAt 1025 (.Dup ⟨2, by decide⟩),
   opAt 1026 (.Dup ⟨1, by decide⟩),
   opAt 1027 .GT,
   pushAt 1028 2 1238,
   opAt 1029 .JUMPI]

/-- Instructions 1672..1726, pc 2595..2346. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1030 .POP,
   opAt 1031 .POP,
   opAt 1032 .POP,
   pushAt 1033 2 4336,
   opAt 1034 .JUMP]

/-- Instructions 1600..1753, pc 2347..2379. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1035 .JUMPDEST,
   pushAt 1036 2 2688,
   opAt 1037 .MLOAD,
   opAt 1038 (.Dup ⟨0, by decide⟩),
   opAt 1039 (.Dup ⟨2, by decide⟩),
   opAt 1040 .ADD,
   pushAt 1041 1 32,
   opAt 1042 (.Swap ⟨0, by decide⟩),
   opAt 1043 .SUB,
   opAt 1044 (.Dup ⟨1, by decide⟩),
   opAt 1045 (.Dup ⟨4, by decide⟩),
   opAt 1046 .ADD,
   pushAt 1047 1 32,
   opAt 1048 (.Swap ⟨0, by decide⟩),
   opAt 1049 .SUB,
   opAt 1050 (.Swap ⟨2, by decide⟩),
   opAt 1051 .POP,
   opAt 1052 (.Swap ⟨2, by decide⟩),
   opAt 1053 .POP,
   opAt 1054 .POP,
   pushAt 1055 2 2784,
   opAt 1056 .MLOAD,
   pushAt 1057 0 0,
   opAt 1058 (.Swap ⟨2, by decide⟩),
   opAt 1059 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
