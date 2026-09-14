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
  [opAt 1003 .POP,
   opAt 1004 .POP,
   opAt 1005 (.Swap ⟨1, by decide⟩),
   opAt 1006 .POP,
   opAt 1007 .POP,
   opAt 1008 (.Dup ⟨0, by decide⟩),
   pushAt 1009 2 2080,
   opAt 1010 .MLOAD,
   opAt 1011 .ADD,
   opAt 1012 (.Dup ⟨0, by decide⟩),
   pushAt 1013 2 2112,
   opAt 1014 .MSTORE,
   opAt 1015 .LT,
   pushAt 1016 2 2048,
   opAt 1017 .MLOAD,
   opAt 1018 .ADD,
   pushAt 1019 2 2080,
   opAt 1020 .MSTORE,
   pushAt 1021 1 31,
   opAt 1022 .NOT,
   opAt 1023 .ADD,
   opAt 1024 (.Dup ⟨2, by decide⟩),
   opAt 1025 (.Dup ⟨1, by decide⟩),
   opAt 1026 .GT,
   pushAt 1027 2 1238,
   opAt 1028 .JUMPI]

/-- Instructions 1672..1726, pc 2595..2346. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1029 .POP,
   opAt 1030 .POP,
   opAt 1031 .POP,
   pushAt 1032 2 4325,
   opAt 1033 .JUMP]

/-- Instructions 1600..1753, pc 2347..2379. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1034 .JUMPDEST,
   pushAt 1035 2 2688,
   opAt 1036 .MLOAD,
   opAt 1037 (.Dup ⟨0, by decide⟩),
   opAt 1038 (.Dup ⟨2, by decide⟩),
   opAt 1039 .ADD,
   pushAt 1040 1 32,
   opAt 1041 (.Swap ⟨0, by decide⟩),
   opAt 1042 .SUB,
   opAt 1043 (.Dup ⟨1, by decide⟩),
   opAt 1044 (.Dup ⟨4, by decide⟩),
   opAt 1045 .ADD,
   pushAt 1046 1 32,
   opAt 1047 (.Swap ⟨0, by decide⟩),
   opAt 1048 .SUB,
   opAt 1049 (.Swap ⟨2, by decide⟩),
   opAt 1050 .POP,
   opAt 1051 (.Swap ⟨2, by decide⟩),
   opAt 1052 .POP,
   opAt 1053 .POP,
   pushAt 1054 2 2784,
   opAt 1055 .MLOAD,
   pushAt 1056 0 0,
   opAt 1057 (.Swap ⟨2, by decide⟩),
   opAt 1058 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
