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
  [opAt 924 .POP,
   opAt 925 .POP,
   opAt 926 (.Swap ⟨1, by decide⟩),
   opAt 927 .POP,
   opAt 928 .POP,
   opAt 929 (.Dup ⟨0, by decide⟩),
   pushAt 930 2 2080,
   opAt 931 .MLOAD,
   opAt 932 .ADD,
   opAt 933 (.Dup ⟨0, by decide⟩),
   pushAt 934 2 2112,
   opAt 935 .MSTORE,
   opAt 936 .LT,
   pushAt 937 2 2048,
   opAt 938 .MLOAD,
   opAt 939 .ADD,
   pushAt 940 2 2080,
   opAt 941 .MSTORE,
   pushAt 942 1 31,
   opAt 943 .NOT,
   opAt 944 .ADD,
   opAt 945 (.Dup ⟨2, by decide⟩),
   opAt 946 (.Dup ⟨1, by decide⟩),
   opAt 947 .GT,
   pushAt 948 2 1120,
   opAt 949 .JUMPI]

/-- Instructions 1672..1726, pc 2595..2346. -/
def blk1595 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 950 .POP,
   opAt 951 .POP,
   opAt 952 .POP,
   pushAt 953 2 4128,
   opAt 954 .JUMP]

/-- Instructions 1600..1753, pc 2347..2379. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 955 .JUMPDEST,
   pushAt 956 2 2688,
   opAt 957 .MLOAD,
   opAt 958 (.Dup ⟨0, by decide⟩),
   opAt 959 (.Dup ⟨2, by decide⟩),
   opAt 960 .ADD,
   pushAt 961 1 31,
   opAt 962 .NOT,
   opAt 963 .ADD,
   opAt 964 (.Dup ⟨1, by decide⟩),
   opAt 965 (.Dup ⟨4, by decide⟩),
   opAt 966 .ADD,
   pushAt 967 1 31,
   opAt 968 .NOT,
   opAt 969 .ADD,
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
