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
  [opAt 1112 .JUMPDEST,
   opAt 1113 (.Dup ⟨0, by decide⟩),
   pushAt 1114 2 2816,
   opAt 1115 .MLOAD,
   opAt 1116 .ADD,
   opAt 1117 .CALLDATALOAD,
   pushAt 1118 0 0,
   opAt 1119 .BYTE,
   opAt 1120 (.Dup ⟨1, by decide⟩),
   opAt 1121 .ISZERO,
   pushAt 1122 2 1582,
   opAt 1123 .JUMPI]

/-- Instructions 1790..1920, pc 2711..3077: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1124 1 128,
   pushAt 1125 2 951,
   opAt 1126 .JUMP]

/-- Instructions 1875..1942, pc 2720..3189: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1127 .JUMPDEST,
   opAt 1128 (.Dup ⟨0, by decide⟩),
   opAt 1129 (.Dup ⟨0, by decide⟩),
   pushAt 1130 1 1,
   opAt 1131 .SHR,
   opAt 1132 .OR,
   opAt 1133 (.Dup ⟨0, by decide⟩),
   pushAt 1134 1 2,
   opAt 1135 .SHR,
   opAt 1136 .OR,
   opAt 1137 (.Dup ⟨0, by decide⟩),
   pushAt 1138 1 4,
   opAt 1139 .SHR,
   opAt 1140 .OR,
   pushAt 1141 1 1,
   opAt 1142 .SHR,
   pushAt 1143 1 1,
   opAt 1144 .ADD,
   pushAt 1145 2 2421,
   opAt 1146 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
