import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 5 (instructions 1255..1313). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1255..1263, pc 1736..1754. -/
def blk1255 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 979 .JUMPDEST,
   opAt 980 .POP,
   opAt 981 .POP,
   pushAt 982 2 1336,
   pushAt 983 2 2048,
   pushAt 984 2 6144,
   pushAt 985 2 1024,
   pushAt 986 2 3779,
   opAt 987 .JUMP]

/-- Instructions 1264..1264, pc 1755..1755. -/
def blk1264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 988 .JUMPDEST]

/-- Instructions 1272..1278, pc 1769..1777. -/
def blk1272 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 991 .JUMPDEST,
   opAt 992 (.Dup ⟨4, by decide⟩),
   opAt 993 (.Dup ⟨1, by decide⟩),
   opAt 994 .EQ,
   pushAt 995 2 1412,
   opAt 996 .JUMPI]

/-- Instructions 1279..1286, pc 1778..1787. -/
def blk1279 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 997 2 1969,
   opAt 998 .JUMP]

/-- Instructions 1287..1293, pc 1789..1805. -/
def blk1287 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 999 .JUMPDEST,
   pushAt 1000 2 1368,
   pushAt 1001 2 1024,
   opAt 1002 (.Dup ⟨0, by decide⟩),
   pushAt 1003 2 1024,
   pushAt 1004 2 3779,
   opAt 1005 .JUMP]

/-- Instructions 1294..1300, pc 1806..1814. -/
def blk1294 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1006 .JUMPDEST,
   opAt 1007 (.Dup ⟨1, by decide⟩),
   opAt 1008 (.Dup ⟨1, by decide⟩),
   opAt 1009 .AND,
   opAt 1010 .ISZERO,
   pushAt 1011 2 1394,
   opAt 1012 .JUMPI]

/-- Instructions 1301..1306, pc 1815..1830. -/
def blk1301 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1013 2 1393,
   pushAt 1014 2 1024,
   pushAt 1015 2 2048,
   pushAt 1016 2 1024,
   pushAt 1017 2 3779,
   opAt 1018 .JUMP]

/-- Instructions 1307..1307, pc 1831..1831. -/
def blk1307 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1019 .JUMPDEST]

/-- Instructions 1308..1313, pc 1832..1840. -/
def blk1308 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1020 .JUMPDEST,
   pushAt 1021 1 1,
   opAt 1022 .SHR,
   opAt 1023 (.Dup ⟨0, by decide⟩),
   pushAt 1024 2 1353,
   opAt 1025 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
