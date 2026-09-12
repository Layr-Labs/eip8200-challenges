import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 4 (instructions 1195..1254). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1195..1196, pc 1639..1642: jump to the appended full-base
dispatcher. The remaining decoded instructions through index 1215 are
unreachable padding, preserving the old loop head at index 1216 / pc 1668. -/
def blk1195 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 939 2 2739,
   opAt 940 .JUMP]

/-- Instructions 1216..1222, pc 1668..1676. -/
def blk1216 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 941 .JUMPDEST,
   opAt 942 (.Dup ⟨1, by decide⟩),
   opAt 943 (.Dup ⟨1, by decide⟩),
   opAt 944 .EQ,
   pushAt 945 2 1317,
   opAt 946 .JUMPI]

/-- Instructions 1223..1228, pc 1677..1692. -/
def blk1223 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 947 2 1274,
   pushAt 948 2 1024,
   pushAt 949 2 5120,
   pushAt 950 2 1024,
   pushAt 951 2 3779,
   opAt 952 .JUMP]

/-- Instructions 1229..1249, pc 1693..1727. -/
def blk1229 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 953 .JUMPDEST,
   opAt 954 (.Dup ⟨0, by decide⟩),
   opAt 955 (.Dup ⟨2, by decide⟩),
   opAt 956 .SUB,
   pushAt 957 1 5,
   opAt 958 .SHL,
   opAt 959 (.Dup ⟨5, by decide⟩),
   opAt 960 .SUB,
   pushAt 961 1 96,
   opAt 962 .ADD,
   opAt 963 .CALLDATALOAD,
   opAt 964 (.Dup ⟨3, by decide⟩),
   pushAt 965 2 3040,
   opAt 966 .ADD,
   opAt 967 .MSTORE,
   pushAt 968 2 1309,
   pushAt 969 2 1024,
   pushAt 970 2 3072,
   pushAt 971 2 1024,
   pushAt 972 2 1765,
   opAt 973 .JUMP]

/-- Instructions 1250..1254, pc 1728..1735. -/
def blk1250 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 974 .JUMPDEST,
   pushAt 975 1 1,
   opAt 976 .ADD,
   pushAt 977 2 1250,
   opAt 978 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
