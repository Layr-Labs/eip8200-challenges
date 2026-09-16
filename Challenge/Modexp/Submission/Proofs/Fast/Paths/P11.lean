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
  [opAt 926 .POP,
   opAt 927 .POP,
   opAt 928 (.Swap ⟨1, by decide⟩),
   opAt 929 .POP,
   opAt 930 .POP,
   opAt 931 (.Dup ⟨0, by decide⟩),
   pushAt 932 2 2080,
   opAt 933 .MLOAD,
   opAt 934 .ADD,
   opAt 935 (.Dup ⟨0, by decide⟩),
   pushAt 936 2 2112,
   opAt 937 .MSTORE,
   opAt 938 .LT,
   pushAt 939 2 2048,
   opAt 940 .MLOAD,
   opAt 941 .ADD,
   pushAt 942 2 2080,
   opAt 943 .MSTORE,
   pushAt 944 1 31,
   opAt 945 .NOT,
   opAt 946 .ADD,
   opAt 947 (.Dup ⟨2, by decide⟩),
   opAt 948 (.Dup ⟨1, by decide⟩),
   opAt 949 .GT,
   pushAt 950 2 1121,
   opAt 951 .JUMPI]

/-- Instructions 1672..1726, pc 2595..2346. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 952 .POP,
   opAt 953 .POP,
   opAt 954 .POP,
   pushAt 955 2 4132,
   opAt 956 .JUMP]

/-- Instructions 1600..1753, pc 2347..2379. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 957 .JUMPDEST,
   pushAt 958 2 2688,
   opAt 959 .MLOAD,
   pushAt 960 2 32,
   opAt 961 (.Dup ⟨1, by decide⟩),
   opAt 962 (.Dup ⟨3, by decide⟩),
   opAt 963 .ADD,
   opAt 964 .SUB,
   pushAt 965 2 32,
   opAt 966 (.Dup ⟨2, by decide⟩),
   opAt 967 (.Dup ⟨5, by decide⟩),
   opAt 968 .ADD,
   opAt 969 .SUB,
   opAt 970 (.Swap ⟨2, by decide⟩),
   opAt 971 .POP,
   opAt 972 (.Swap ⟨2, by decide⟩),
   opAt 973 .POP,
   opAt 974 .POP,
   pushAt 975 2 2784,
   opAt 976 .MLOAD,
   pushAt 977 0 0,
   opAt 978 (.Swap ⟨2, by decide⟩),
   opAt 979 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
