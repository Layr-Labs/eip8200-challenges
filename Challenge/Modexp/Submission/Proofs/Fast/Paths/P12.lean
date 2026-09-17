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
  [opAt 980 .JUMPDEST,
   opAt 981 (.Dup ⟨1 , by decide⟩),
   opAt 982 .MLOAD,
   opAt 983 (.Dup ⟨3 , by decide⟩),
   opAt 984 .MLOAD,
   opAt 985 (.Dup ⟨1 , by decide⟩),
   opAt 986 .ADD,
   opAt 987 (.Swap ⟨0 , by decide⟩),
   opAt 988 (.Dup ⟨1 , by decide⟩),
   opAt 989 .LT,
   opAt 990 (.Swap ⟨0 , by decide⟩),
   opAt 991 (.Dup ⟨5 , by decide⟩),
   opAt 992 .ADD,
   opAt 993 (.Swap ⟨4 , by decide⟩),
   opAt 994 (.Dup ⟨5 , by decide⟩),
   opAt 995 .LT,
   opAt 996 .OR,
   opAt 997 (.Swap ⟨3 , by decide⟩),
   opAt 998 (.Dup ⟨1 , by decide⟩),
   opAt 999 .MSTORE,
   pushAt 1000 1 32,
   pushAt 1001 1 32,
   pushAt 1002 1 32,
   opAt 1003 (.Swap ⟨2 , by decide⟩),
   opAt 1004 .SUB,
   opAt 1005 (.Swap ⟨2 , by decide⟩),
   opAt 1006 .SUB,
   opAt 1007 (.Swap ⟨2 , by decide⟩),
   opAt 1008 .SUB,
   opAt 1009 (.Swap ⟨1 , by decide⟩),
   opAt 1010 (.Swap ⟨0 , by decide⟩),
   pushAt 1011 2 2080,
   opAt 1012 (.Dup ⟨1 , by decide⟩),
   opAt 1013 .GT,
   pushAt 1014 2 1389,
   opAt 1015 .JUMPI]

/-- Instructions 1792..1745, pc 2770..2431. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1016 .POP,
   opAt 1017 .POP,
   opAt 1018 .POP,
   pushAt 1019 2 2080,
   opAt 1020 .MSTORE,
   pushAt 1021 2 4132,
   opAt 1022 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
