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
  [opAt 860 .JUMPDEST,
   pushAt 861 1 64,
   opAt 862 .CALLDATALOAD,
   opAt 863 (.Dup ⟨0, by decide⟩),
   pushAt 864 1 33,
   opAt 865 .GT,
   pushAt 866 2 1581,
   opAt 867 .JUMPI]

/-- Instructions 986..989, pc 1133..1137.  The EIP-7823 oversize test that used to
follow the two header loads (13 instructions, `DUP3 PUSH2 1024 LT DUP3 PUSH2 1024 LT OR
DUP2 PUSH2 1024 LT OR PUSH2 <BAIL3> JUMPI`) is gone from the bytecode: `ValidInput`
bounds every declared size by 1024, so its `JUMPI` was never taken.  The block now falls
straight through to the top-limb block at instruction 872, pc 1138. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 868 1 32,
   opAt 869 .CALLDATALOAD,
   pushAt 870 0 0,
   opAt 871 .CALLDATALOAD]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 872 (.Dup ⟨2, by decide⟩),
   pushAt 873 1 31,
   opAt 874 .ADD,
   pushAt 875 1 5,
   opAt 876 .SHR,
   opAt 877 (.Dup ⟨0, by decide⟩),
   pushAt 878 1 5,
   opAt 879 .SHL,
   opAt 880 (.Dup ⟨3, by decide⟩),
   opAt 881 (.Dup ⟨3, by decide⟩),
   opAt 882 .ADD,
   pushAt 883 1 96,
   opAt 884 .ADD,
   opAt 885 (.Dup ⟨5, by decide⟩),
   opAt 886 (.Dup ⟨2, by decide⟩),
   opAt 887 .SUB,
   pushAt 888 1 3,
   opAt 889 .SHL,
   opAt 890 (.Dup ⟨1, by decide⟩),
   opAt 891 .CALLDATALOAD,
   opAt 892 (.Swap ⟨0, by decide⟩),
   opAt 893 .SHR,
   opAt 894 .ISZERO,
   pushAt 895 2 1587,
   opAt 896 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
