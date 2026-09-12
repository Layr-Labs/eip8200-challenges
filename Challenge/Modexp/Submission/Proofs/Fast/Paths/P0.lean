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
   pushAt 941 2 1716,
   opAt 942 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 943 1 32,
   opAt 944 .CALLDATALOAD,
   pushAt 945 0 0,
   opAt 946 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 947 (.Dup ⟨2, by decide⟩),
   pushAt 948 1 31,
   opAt 949 .ADD,
   pushAt 950 1 5,
   opAt 951 .SHR,
   opAt 952 (.Dup ⟨0, by decide⟩),
   pushAt 953 1 5,
   opAt 954 .SHL,
   opAt 955 (.Dup ⟨3, by decide⟩),
   opAt 956 (.Dup ⟨3, by decide⟩),
   opAt 957 .ADD,
   pushAt 958 1 96,
   opAt 959 .ADD,
   opAt 960 (.Dup ⟨5, by decide⟩),
   opAt 961 (.Dup ⟨2, by decide⟩),
   opAt 962 .SUB,
   pushAt 963 1 3,
   opAt 964 .SHL,
   opAt 965 (.Dup ⟨1, by decide⟩),
   opAt 966 .CALLDATALOAD,
   opAt 967 (.Swap ⟨0, by decide⟩),
   opAt 968 .SHR,
   opAt 969 .ISZERO,
   pushAt 970 2 1722,
   opAt 971 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
