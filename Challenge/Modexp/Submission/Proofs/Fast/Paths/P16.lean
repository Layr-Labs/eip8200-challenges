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
  [opAt 1111 .JUMPDEST,
   opAt 1112 (.Dup ⟨0, by decide⟩),
   pushAt 1113 2 2816,
   opAt 1114 .MLOAD,
   opAt 1115 .ADD,
   opAt 1116 .CALLDATALOAD,
   pushAt 1117 0 0,
   opAt 1118 .BYTE,
   opAt 1119 (.Dup ⟨1, by decide⟩),
   opAt 1120 .ISZERO,
   pushAt 1121 2 1582,
   opAt 1122 .JUMPI]

/-- Instructions 1790..1920, pc 2711..3077: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1123 1 128,
   pushAt 1124 2 951,
   opAt 1125 .JUMP]

/-- Instructions 1875..1942, pc 2720..3189: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1126 .JUMPDEST,
   opAt 1127 (.Dup ⟨0, by decide⟩),
   opAt 1128 (.Dup ⟨0, by decide⟩),
   pushAt 1129 1 1,
   opAt 1130 .SHR,
   opAt 1131 .OR,
   opAt 1132 (.Dup ⟨0, by decide⟩),
   pushAt 1133 1 2,
   opAt 1134 .SHR,
   opAt 1135 .OR,
   opAt 1136 (.Dup ⟨0, by decide⟩),
   pushAt 1137 1 4,
   opAt 1138 .SHR,
   opAt 1139 .OR,
   pushAt 1140 1 1,
   opAt 1141 .SHR,
   pushAt 1142 1 1,
   opAt 1143 .ADD,
   pushAt 1144 2 2421,
   opAt 1145 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
