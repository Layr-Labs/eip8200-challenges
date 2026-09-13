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
  [opAt 931 .JUMPDEST,
   pushAt 932 1 64,
   opAt 933 .CALLDATALOAD,
   opAt 934 (.Dup ⟨0, by decide⟩),
   pushAt 935 1 33,
   opAt 936 (.Swap ⟨0, by decide⟩),
   opAt 937 .SUB,
   pushAt 938 1 223,
   opAt 939 .LT,
   pushAt 940 2 1708,
   opAt 941 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 942 1 32,
   opAt 943 .CALLDATALOAD,
   pushAt 944 0 0,
   opAt 945 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 946 (.Dup ⟨2, by decide⟩),
   pushAt 947 1 31,
   opAt 948 .ADD,
   pushAt 949 1 5,
   opAt 950 .SHR,
   opAt 951 (.Dup ⟨0, by decide⟩),
   pushAt 952 1 5,
   opAt 953 .SHL,
   opAt 954 (.Dup ⟨3, by decide⟩),
   opAt 955 (.Dup ⟨3, by decide⟩),
   opAt 956 .ADD,
   pushAt 957 1 96,
   opAt 958 .ADD,
   opAt 959 (.Dup ⟨5, by decide⟩),
   opAt 960 (.Dup ⟨2, by decide⟩),
   opAt 961 .SUB,
   pushAt 962 1 3,
   opAt 963 .SHL,
   opAt 964 (.Dup ⟨1, by decide⟩),
   opAt 965 .CALLDATALOAD,
   opAt 966 (.Swap ⟨0, by decide⟩),
   opAt 967 .SHR,
   opAt 968 .ISZERO,
   pushAt 969 2 1714,
   opAt 970 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
