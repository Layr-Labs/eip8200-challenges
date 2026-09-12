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
   opAt 940 (.Swap ⟨0, by decide⟩),
   opAt 941 .SUB,
   pushAt 942 1 223,
   opAt 943 .LT,
   pushAt 944 2 1716,
   opAt 945 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 946 1 32,
   opAt 947 .CALLDATALOAD,
   pushAt 948 0 0,
   opAt 949 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 950 (.Dup ⟨2, by decide⟩),
   pushAt 951 1 31,
   opAt 952 .ADD,
   pushAt 953 1 5,
   opAt 954 .SHR,
   opAt 955 (.Dup ⟨0, by decide⟩),
   pushAt 956 1 5,
   opAt 957 .SHL,
   opAt 958 (.Dup ⟨3, by decide⟩),
   opAt 959 (.Dup ⟨3, by decide⟩),
   opAt 960 .ADD,
   pushAt 961 1 96,
   opAt 962 .ADD,
   opAt 963 (.Dup ⟨5, by decide⟩),
   opAt 964 (.Dup ⟨2, by decide⟩),
   opAt 965 .SUB,
   pushAt 966 1 3,
   opAt 967 .SHL,
   opAt 968 (.Dup ⟨1, by decide⟩),
   opAt 969 .CALLDATALOAD,
   opAt 970 (.Swap ⟨0, by decide⟩),
   opAt 971 .SHR,
   opAt 972 .ISZERO,
   pushAt 973 2 1722,
   opAt 974 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
