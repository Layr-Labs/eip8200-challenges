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
  [opAt 1006 .POP,
   opAt 1007 .POP,
   opAt 1008 (.Swap ⟨1, by decide⟩),
   opAt 1009 .POP,
   opAt 1010 .POP,
   opAt 1011 (.Dup ⟨0, by decide⟩),
   pushAt 1012 2 2080,
   opAt 1013 .MLOAD,
   opAt 1014 .ADD,
   opAt 1015 (.Dup ⟨0, by decide⟩),
   pushAt 1016 2 2112,
   opAt 1017 .MSTORE,
   opAt 1018 .LT,
   pushAt 1019 2 2048,
   opAt 1020 .MLOAD,
   opAt 1021 .ADD,
   pushAt 1022 2 2080,
   opAt 1023 .MSTORE,
   pushAt 1024 1 31,
   opAt 1025 .NOT,
   opAt 1026 .ADD,
   opAt 1027 (.Dup ⟨2, by decide⟩),
   opAt 1028 (.Dup ⟨1, by decide⟩),
   opAt 1029 .GT,
   pushAt 1030 2 1242,
   opAt 1031 .JUMPI]

/-- Instructions 1672..1726, pc 2595..2346. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1032 .POP,
   opAt 1033 .POP,
   opAt 1034 .POP,
   pushAt 1035 2 4347,
   opAt 1036 .JUMP]

/-- Instructions 1600..1753, pc 2347..2379. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1037 .JUMPDEST,
   pushAt 1038 2 2688,
   opAt 1039 .MLOAD,
   opAt 1040 (.Dup ⟨0, by decide⟩),
   opAt 1041 (.Dup ⟨2, by decide⟩),
   opAt 1042 .ADD,
   pushAt 1043 1 32,
   opAt 1044 (.Swap ⟨0, by decide⟩),
   opAt 1045 .SUB,
   opAt 1046 (.Dup ⟨1, by decide⟩),
   opAt 1047 (.Dup ⟨4, by decide⟩),
   opAt 1048 .ADD,
   pushAt 1049 1 32,
   opAt 1050 (.Swap ⟨0, by decide⟩),
   opAt 1051 .SUB,
   opAt 1052 (.Swap ⟨2, by decide⟩),
   opAt 1053 .POP,
   opAt 1054 (.Swap ⟨2, by decide⟩),
   opAt 1055 .POP,
   opAt 1056 .POP,
   pushAt 1057 2 2784,
   opAt 1058 .MLOAD,
   pushAt 1059 0 0,
   opAt 1060 (.Swap ⟨2, by decide⟩),
   opAt 1061 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
