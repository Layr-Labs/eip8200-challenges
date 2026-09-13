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
  [opAt 1195 .JUMPDEST,
   opAt 1196 (.Dup ⟨0, by decide⟩),
   pushAt 1197 2 2816,
   opAt 1198 .MLOAD,
   opAt 1199 .ADD,
   opAt 1200 .CALLDATALOAD,
   pushAt 1201 0 0,
   opAt 1202 .BYTE,
   opAt 1203 (.Dup ⟨1, by decide⟩),
   opAt 1204 .ISZERO,
   pushAt 1205 2 1713,
   opAt 1206 .JUMPI]

/-- Instructions 1790..1920, pc 2711..3077: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1207 1 128,
   pushAt 1208 2 1073,
   opAt 1209 .JUMP]

/-- Instructions 1875..1942, pc 2720..3189: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1210 .JUMPDEST,
   opAt 1211 (.Dup ⟨0, by decide⟩),
   opAt 1212 (.Dup ⟨0, by decide⟩),
   pushAt 1213 1 1,
   opAt 1214 .SHR,
   opAt 1215 .OR,
   opAt 1216 (.Dup ⟨0, by decide⟩),
   pushAt 1217 1 2,
   opAt 1218 .SHR,
   opAt 1219 .OR,
   opAt 1220 (.Dup ⟨0, by decide⟩),
   pushAt 1221 1 4,
   opAt 1222 .SHR,
   opAt 1223 .OR,
   pushAt 1224 1 1,
   opAt 1225 .SHR,
   pushAt 1226 1 1,
   opAt 1227 .ADD,
   pushAt 1228 2 2653,
   opAt 1229 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
