import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 0 (instructions 1030..1080). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1030..1038, pc 1314..1374. -/
def blk977 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 895 .JUMPDEST,
   pushAt 896 1 64,
   opAt 897 .CALLDATALOAD,
   opAt 898 (.Dup ⟨0, by decide⟩),
   pushAt 899 1 33,
   opAt 900 .GT,
   pushAt 901 2 1629,
   opAt 902 .JUMPI]

/-- Instructions 1039..1042, pc 1181..1185.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 925, pc 1186. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 903 1 32,
   opAt 904 .CALLDATALOAD,
   pushAt 905 0 0,
   opAt 906 .CALLDATALOAD]

/-- Instructions 1003..1080, pc 1353..1432. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 907 (.Dup ⟨2, by decide⟩),
   pushAt 908 1 31,
   opAt 909 .ADD,
   pushAt 910 1 5,
   opAt 911 .SHR,
   opAt 912 (.Dup ⟨0, by decide⟩),
   pushAt 913 1 5,
   opAt 914 .SHL,
   opAt 915 (.Dup ⟨3, by decide⟩),
   opAt 916 (.Dup ⟨3, by decide⟩),
   opAt 917 .ADD,
   pushAt 918 1 96,
   opAt 919 .ADD,
   opAt 920 (.Dup ⟨5, by decide⟩),
   opAt 921 (.Dup ⟨2, by decide⟩),
   opAt 922 .SUB,
   pushAt 923 1 3,
   opAt 924 .SHL,
   opAt 925 (.Dup ⟨1, by decide⟩),
   opAt 926 .CALLDATALOAD,
   opAt 927 (.Swap ⟨0, by decide⟩),
   opAt 928 .SHR,
   opAt 929 .ISZERO,
   pushAt 930 2 1635,
   opAt 931 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
