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
  [opAt 1194 .JUMPDEST,
   opAt 1195 (.Dup ⟨0, by decide⟩),
   pushAt 1196 2 2816,
   opAt 1197 .MLOAD,
   opAt 1198 .ADD,
   opAt 1199 .CALLDATALOAD,
   pushAt 1200 0 0,
   opAt 1201 .BYTE,
   opAt 1202 (.Dup ⟨1, by decide⟩),
   opAt 1203 .ISZERO,
   pushAt 1204 2 1701,
   opAt 1205 .JUMPI]

/-- Instructions 1790..1920, pc 2711..3077: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1206 1 128,
   pushAt 1207 2 1061,
   opAt 1208 .JUMP]

/-- Instructions 1875..1942, pc 2720..3189: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1209 .JUMPDEST,
   opAt 1210 (.Dup ⟨0, by decide⟩),
   opAt 1211 (.Dup ⟨0, by decide⟩),
   pushAt 1212 1 1,
   opAt 1213 .SHR,
   opAt 1214 .OR,
   opAt 1215 (.Dup ⟨0, by decide⟩),
   pushAt 1216 1 2,
   opAt 1217 .SHR,
   opAt 1218 .OR,
   opAt 1219 (.Dup ⟨0, by decide⟩),
   pushAt 1220 1 4,
   opAt 1221 .SHR,
   opAt 1222 .OR,
   pushAt 1223 1 1,
   opAt 1224 .SHR,
   pushAt 1225 1 1,
   opAt 1226 .ADD,
   pushAt 1227 2 2615,
   opAt 1228 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
