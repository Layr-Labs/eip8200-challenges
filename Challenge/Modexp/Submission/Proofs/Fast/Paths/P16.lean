import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1908..1941).

`LZ` (pc 2690) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1908..1792, pc 2690..3071) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1789..1920, pc 2711..3077) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1874..1941, pc 2720..3184) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1908..1792, pc 2690..3071: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1192 .JUMPDEST,
   opAt 1193 (.Dup ⟨0, by decide⟩),
   pushAt 1194 2 2816,
   opAt 1195 .MLOAD,
   opAt 1196 .ADD,
   opAt 1197 .CALLDATALOAD,
   pushAt 1198 0 0,
   opAt 1199 .BYTE,
   opAt 1200 (.Dup ⟨1, by decide⟩),
   opAt 1201 .ISZERO,
   pushAt 1202 2 1700,
   opAt 1203 .JUMPI]

/-- Instructions 1789..1920, pc 2711..3077: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1204 1 128,
   pushAt 1205 2 1060,
   opAt 1206 .JUMP]

/-- Instructions 1874..1941, pc 2720..3184: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1207 .JUMPDEST,
   opAt 1208 (.Dup ⟨0, by decide⟩),
   opAt 1209 (.Dup ⟨0, by decide⟩),
   pushAt 1210 1 1,
   opAt 1211 .SHR,
   opAt 1212 .OR,
   opAt 1213 (.Dup ⟨0, by decide⟩),
   pushAt 1214 1 2,
   opAt 1215 .SHR,
   opAt 1216 .OR,
   opAt 1217 (.Dup ⟨0, by decide⟩),
   pushAt 1218 1 4,
   opAt 1219 .SHR,
   opAt 1220 .OR,
   pushAt 1221 1 1,
   opAt 1222 .SHR,
   pushAt 1223 1 1,
   opAt 1224 .ADD,
   pushAt 1225 2 2609,
   opAt 1226 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
