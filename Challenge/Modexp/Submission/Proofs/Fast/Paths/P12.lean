import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1754..1809). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1754..1788, pc 2380..2769. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 982 .JUMPDEST,
   opAt 983 (.Dup ⟨1 , by decide⟩),
   opAt 984 .MLOAD,
   opAt 985 (.Dup ⟨3 , by decide⟩),
   opAt 986 .MLOAD,
   opAt 987 (.Dup ⟨1 , by decide⟩),
   opAt 988 .ADD,
   opAt 989 (.Swap ⟨0 , by decide⟩),
   opAt 990 (.Dup ⟨1 , by decide⟩),
   opAt 991 .LT,
   opAt 992 (.Swap ⟨0 , by decide⟩),
   opAt 993 (.Dup ⟨5 , by decide⟩),
   opAt 994 .ADD,
   opAt 995 (.Swap ⟨4 , by decide⟩),
   opAt 996 (.Dup ⟨5 , by decide⟩),
   opAt 997 .LT,
   opAt 998 .OR,
   opAt 999 (.Swap ⟨3 , by decide⟩),
   opAt 1000 (.Dup ⟨1 , by decide⟩),
   opAt 1001 .MSTORE,
   pushAt 1002 1 32,
   pushAt 1003 1 32,
   pushAt 1004 1 32,
   opAt 1005 (.Swap ⟨2 , by decide⟩),
   opAt 1006 .SUB,
   opAt 1007 (.Swap ⟨2 , by decide⟩),
   opAt 1008 .SUB,
   opAt 1009 (.Swap ⟨2 , by decide⟩),
   opAt 1010 .SUB,
   opAt 1011 (.Swap ⟨1 , by decide⟩),
   opAt 1012 (.Swap ⟨0 , by decide⟩),
   pushAt 1013 2 2080,
   opAt 1014 (.Dup ⟨1 , by decide⟩),
   opAt 1015 .GT,
   pushAt 1016 2 1389,
   opAt 1017 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2431. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1018 .POP,
   opAt 1019 .POP,
   opAt 1020 .POP,
   pushAt 1021 2 2080,
   opAt 1022 .MSTORE,
   pushAt 1023 2 4132,
   opAt 1024 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
