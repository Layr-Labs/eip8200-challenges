import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1908..1942).

`LZ` (pc 2695) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1908..1792, pc 2695..3071) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1790..1920, pc 2711..3077) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1875..1942, pc 2720..3189) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1908..1792, pc 2695..3071: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1113 .JUMPDEST,
   opAt 1114 (.Dup ⟨0, by decide⟩),
   pushAt 1115 2 2816,
   opAt 1116 .MLOAD,
   opAt 1117 .ADD,
   opAt 1118 .CALLDATALOAD,
   pushAt 1119 0 0,
   opAt 1120 .BYTE,
   opAt 1121 (.Dup ⟨1, by decide⟩),
   opAt 1122 .ISZERO,
   pushAt 1123 2 1582,
   opAt 1124 .JUMPI]

/-- Instructions 1790..1920, pc 2711..3077: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1125 1 128,
   pushAt 1126 2 951,
   opAt 1127 .JUMP]

/-- Instructions 1875..1942, pc 2720..3189: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1128 .JUMPDEST,
   opAt 1129 (.Dup ⟨0, by decide⟩),
   opAt 1130 (.Dup ⟨0, by decide⟩),
   pushAt 1131 1 1,
   opAt 1132 .SHR,
   opAt 1133 .OR,
   opAt 1134 (.Dup ⟨0, by decide⟩),
   pushAt 1135 1 2,
   opAt 1136 .SHR,
   opAt 1137 .OR,
   opAt 1138 (.Dup ⟨0, by decide⟩),
   pushAt 1139 1 4,
   opAt 1140 .SHR,
   opAt 1141 .OR,
   pushAt 1142 1 1,
   opAt 1143 .SHR,
   pushAt 1144 1 1,
   opAt 1145 .ADD,
   pushAt 1146 2 2421,
   opAt 1147 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
