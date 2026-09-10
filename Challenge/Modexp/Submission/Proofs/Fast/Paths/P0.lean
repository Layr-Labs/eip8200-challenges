import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 0 (instructions 977..1027). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 977..985, pc 1314..1326. -/
def blk977 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 935 .JUMPDEST,
   pushAt 936 1 64,
   opAt 937 .CALLDATALOAD,
   opAt 938 (.Dup ⟨0, by decide⟩),
   pushAt 939 1 33,
   opAt 940 .GT,
   pushAt 941 2 1731,
   opAt 942 .JUMPI]

/-- Instructions 986..1002, pc 1327..1352. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 943 1 32,
   opAt 944 .CALLDATALOAD,
   pushAt 945 0 0,
   opAt 946 .CALLDATALOAD,
   opAt 947 (.Dup ⟨2, by decide⟩),
   pushAt 948 2 1024,
   opAt 949 .LT,
   opAt 950 (.Dup ⟨2, by decide⟩),
   pushAt 951 2 1024,
   opAt 952 .LT,
   opAt 953 .OR,
   opAt 954 (.Dup ⟨1, by decide⟩),
   pushAt 955 2 1024,
   opAt 956 .LT,
   opAt 957 .OR,
   pushAt 958 2 1737,
   opAt 959 .JUMPI]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 960 (.Dup ⟨2, by decide⟩),
   pushAt 961 1 31,
   opAt 962 .ADD,
   pushAt 963 1 5,
   opAt 964 .SHR,
   opAt 965 (.Dup ⟨0, by decide⟩),
   pushAt 966 1 5,
   opAt 967 .SHL,
   opAt 968 (.Dup ⟨3, by decide⟩),
   opAt 969 (.Dup ⟨3, by decide⟩),
   opAt 970 .ADD,
   pushAt 971 1 96,
   opAt 972 .ADD,
   opAt 973 (.Dup ⟨5, by decide⟩),
   opAt 974 (.Dup ⟨2, by decide⟩),
   opAt 975 .SUB,
   pushAt 976 1 3,
   opAt 977 .SHL,
   opAt 978 (.Dup ⟨1, by decide⟩),
   opAt 979 .CALLDATALOAD,
   opAt 980 (.Swap ⟨0, by decide⟩),
   opAt 981 .SHR,
   opAt 982 .ISZERO,
   pushAt 983 2 1745,
   opAt 984 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
