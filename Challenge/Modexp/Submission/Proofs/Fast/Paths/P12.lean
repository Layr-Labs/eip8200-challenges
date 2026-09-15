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
  [opAt 981 .JUMPDEST,
   opAt 982 (.Dup ⟨1 , by decide⟩),
   opAt 983 .MLOAD,
   opAt 984 (.Dup ⟨3 , by decide⟩),
   opAt 985 .MLOAD,
   opAt 986 (.Dup ⟨1 , by decide⟩),
   opAt 987 .ADD,
   opAt 988 (.Swap ⟨0 , by decide⟩),
   opAt 989 (.Dup ⟨1 , by decide⟩),
   opAt 990 .LT,
   opAt 991 (.Swap ⟨0 , by decide⟩),
   opAt 992 (.Dup ⟨5 , by decide⟩),
   opAt 993 .ADD,
   opAt 994 (.Swap ⟨4 , by decide⟩),
   opAt 995 (.Dup ⟨5 , by decide⟩),
   opAt 996 .LT,
   opAt 997 .OR,
   opAt 998 (.Swap ⟨3 , by decide⟩),
   opAt 999 (.Dup ⟨1 , by decide⟩),
   opAt 1000 .MSTORE,
   pushAt 1001 1 32,
   pushAt 1002 1 32,
   pushAt 1003 1 32,
   opAt 1004 (.Swap ⟨2 , by decide⟩),
   opAt 1005 .SUB,
   opAt 1006 (.Swap ⟨2 , by decide⟩),
   opAt 1007 .SUB,
   opAt 1008 (.Swap ⟨2 , by decide⟩),
   opAt 1009 .SUB,
   opAt 1010 (.Swap ⟨1 , by decide⟩),
   opAt 1011 (.Swap ⟨0 , by decide⟩),
   pushAt 1012 2 2080,
   opAt 1013 (.Dup ⟨1 , by decide⟩),
   opAt 1014 .GT,
   pushAt 1015 2 1389,
   opAt 1016 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2431. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1017 .POP,
   opAt 1018 .POP,
   opAt 1019 .POP,
   pushAt 1020 2 2080,
   opAt 1021 .MSTORE,
   pushAt 1022 2 4132,
   opAt 1023 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
