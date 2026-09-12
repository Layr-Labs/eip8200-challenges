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
   pushAt 866 2 1614,
   opAt 867 .JUMPI]

/-- Instructions 986..1002, pc 1327..1352. -/
def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 868 1 32,
   opAt 869 .CALLDATALOAD,
   pushAt 870 0 0,
   opAt 871 .CALLDATALOAD,
   opAt 872 (.Dup ⟨2, by decide⟩),
   pushAt 873 2 256,
   opAt 874 .LT,
   opAt 875 (.Dup ⟨2, by decide⟩),
   pushAt 876 2 256,
   opAt 877 .LT,
   opAt 878 .OR,
   opAt 879 (.Dup ⟨1, by decide⟩),
   pushAt 880 2 256,
   opAt 881 .LT,
   opAt 882 .OR,
   pushAt 883 2 1620,
   opAt 884 .JUMPI]

/-- Instructions 1003..1027, pc 1353..1384. -/
def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 885 (.Dup ⟨2, by decide⟩),
   pushAt 886 1 31,
   opAt 887 .ADD,
   pushAt 888 1 5,
   opAt 889 .SHR,
   opAt 890 (.Dup ⟨0, by decide⟩),
   pushAt 891 1 5,
   opAt 892 .SHL,
   opAt 893 (.Dup ⟨3, by decide⟩),
   opAt 894 (.Dup ⟨3, by decide⟩),
   opAt 895 .ADD,
   pushAt 896 1 96,
   opAt 897 .ADD,
   opAt 898 (.Dup ⟨5, by decide⟩),
   opAt 899 (.Dup ⟨2, by decide⟩),
   opAt 900 .SUB,
   pushAt 901 1 3,
   opAt 902 .SHL,
   opAt 903 (.Dup ⟨1, by decide⟩),
   opAt 904 .CALLDATALOAD,
   opAt 905 (.Swap ⟨0, by decide⟩),
   opAt 906 .SHR,
   opAt 907 .ISZERO,
   pushAt 908 2 1628,
   opAt 909 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
