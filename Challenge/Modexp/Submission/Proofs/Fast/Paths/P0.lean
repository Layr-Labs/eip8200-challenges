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
  [opAt 858 .JUMPDEST,
   pushAt 859 1 64,
   opAt 860 .CALLDATALOAD,
   opAt 861 (.Dup ⟨0, by decide⟩),
   pushAt 862 1 33,
   opAt 863 .GT,
   pushAt 864 2 1577,
   opAt 865 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 866 1 32,
   opAt 867 .CALLDATALOAD,
   pushAt 868 0 0,
   opAt 869 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 870 (.Dup ⟨2, by decide⟩),
   pushAt 871 1 31,
   opAt 872 .ADD,
   pushAt 873 1 5,
   opAt 874 .SHR,
   opAt 875 (.Dup ⟨0, by decide⟩),
   pushAt 876 1 5,
   opAt 877 .SHL,
   opAt 878 (.Dup ⟨3, by decide⟩),
   opAt 879 (.Dup ⟨3, by decide⟩),
   opAt 880 .ADD,
   pushAt 881 1 96,
   opAt 882 .ADD,
   opAt 883 (.Dup ⟨5, by decide⟩),
   opAt 884 (.Dup ⟨2, by decide⟩),
   opAt 885 .SUB,
   pushAt 886 1 3,
   opAt 887 .SHL,
   opAt 888 (.Dup ⟨1, by decide⟩),
   opAt 889 .CALLDATALOAD,
   opAt 890 (.Swap ⟨0, by decide⟩),
   opAt 891 .SHR,
   opAt 892 .ISZERO,
   pushAt 893 2 1583,
   opAt 894 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
