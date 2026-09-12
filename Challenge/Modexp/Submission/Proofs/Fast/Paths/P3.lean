import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 3 (instructions 1138..1194). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1138..1147, pc 1533..1554. -/
def blk1138 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 893 .JUMPDEST,
   pushAt 894 2 9344,
   opAt 895 .MLOAD,
   pushAt 896 2 4096,
   pushAt 897 2 5120,
   opAt 898 .MCOPY,
   pushAt 899 2 2704,
   pushAt 900 2 5120,
   pushAt 901 2 3128,
   opAt 902 .JUMP]

/-- Instructions 1148..1154, pc 1555..1567. -/
def blk1148 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1155..1161, pc 1569..1585. -/
def blk1155 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 903 .JUMPDEST,
   pushAt 904 2 1204,
   pushAt 905 2 6144,
   opAt 906 (.Dup ⟨0, by decide⟩),
   pushAt 907 2 6144,
   pushAt 908 2 3779,
   opAt 909 .JUMP]

/-- Instructions 1162..1173, pc 1586..1604. -/
def blk1162 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 910 .JUMPDEST,
   opAt 911 (.Dup ⟨2, by decide⟩),
   opAt 912 (.Dup ⟨1, by decide⟩),
   opAt 913 .SHR,
   pushAt 914 1 1,
   opAt 915 .AND,
   pushAt 916 2 1024,
   opAt 917 .MUL,
   pushAt 918 2 4096,
   opAt 919 .ADD,
   pushAt 920 2 2018,
   opAt 921 .JUMP]

/-- Instructions 1178..1183, pc 1615..1622. -/
def blk1178 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 922 .JUMPDEST,
   opAt 923 .POP,
   opAt 924 (.Dup ⟨0, by decide⟩),
   opAt 925 .ISZERO,
   pushAt 926 2 1238,
   opAt 927 .JUMPI]

/-- Instructions 1184..1188, pc 1623..1630. -/
def blk1184 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 928 0 0,
   opAt 929 .NOT,
   opAt 930 .ADD,
   pushAt 931 2 1189,
   opAt 932 .JUMP]

/-- Instructions 1189..1194, pc 1631..1638. -/
def blk1189 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 933 .JUMPDEST,
   opAt 934 .POP,
   opAt 935 (.Dup ⟨2, by decide⟩),
   opAt 936 .ISZERO,
   pushAt 937 2 3005,
   opAt 938 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
