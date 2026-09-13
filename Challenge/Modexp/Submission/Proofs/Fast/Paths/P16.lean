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
  [opAt 1193 .JUMPDEST,
   opAt 1194 (.Dup ⟨0, by decide⟩),
   pushAt 1195 2 2816,
   opAt 1196 .MLOAD,
   opAt 1197 .ADD,
   opAt 1198 .CALLDATALOAD,
   pushAt 1199 0 0,
   opAt 1200 .BYTE,
   opAt 1201 (.Dup ⟨1, by decide⟩),
   opAt 1202 .ISZERO,
   pushAt 1203 2 1701,
   opAt 1204 .JUMPI]

/-- Instructions 1790..1920, pc 2711..3077: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1205 1 128,
   pushAt 1206 2 1061,
   opAt 1207 .JUMP]

/-- Instructions 1875..1942, pc 2720..3189: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1208 .JUMPDEST,
   opAt 1209 (.Dup ⟨0, by decide⟩),
   opAt 1210 (.Dup ⟨0, by decide⟩),
   pushAt 1211 1 1,
   opAt 1212 .SHR,
   opAt 1213 .OR,
   opAt 1214 (.Dup ⟨0, by decide⟩),
   pushAt 1215 1 2,
   opAt 1216 .SHR,
   opAt 1217 .OR,
   opAt 1218 (.Dup ⟨0, by decide⟩),
   pushAt 1219 1 4,
   opAt 1220 .SHR,
   opAt 1221 .OR,
   pushAt 1222 1 1,
   opAt 1223 .SHR,
   pushAt 1224 1 1,
   opAt 1225 .ADD,
   pushAt 1226 2 2616,
   opAt 1227 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
