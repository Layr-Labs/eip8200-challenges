import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 18 (instructions 2504..2526).

`LZBASE` (pc 3776) is reached from `LZ`'s byte-0 arm with `[mask, w, i]`.  The
bit loop's first iteration squares the accumulator, which is the Montgomery
form of one and therefore a fixed point, and then multiplies by `BASE` because
the leading bit of a nonzero byte is set, so it always ends holding `BASE`.
This block copies `BASE` into `ACC` and resumes at the mask shift, pc 1832.  A
zero byte has no set bit, so it takes the untouched loop head at pc 1789.

The appended `RRSET` landing (pc 3803) materializes `CC` only after the direct
bit dispatch in the RR chain; its target is the existing MonPro call frame.

* `blk2504` (idx 2504..2508, pc 3776..3782) — the `w = 0` test;
* `blk2509` (idx 2509..2515, pc 3783..3797) — the copy and the resume;
* `blk2516` (idx 2516..2518, pc 3798..3802) — the zero-byte arm;

* `blk2519` (idx 2519..2526, pc 3803..3820) — the direct RR set arm. -/
namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2504..2508, pc 3776..3782: the `w = 0` test. -/
def blk2504 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2504 .JUMPDEST,
   opAt 2505 (.Dup ⟨1, by decide⟩),
   opAt 2506 .ISZERO,
   pushAt 2507 2 3798,
   opAt 2508 .JUMPI]

/-- Instructions 2509..2515, pc 3783..3797: `ACC := BASE`, then the shift. -/
def blk2509 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2509 2 9344,
   opAt 2510 .MLOAD,
   pushAt 2511 2 2048,
   pushAt 2512 2 1024,
   opAt 2513 .MCOPY,
   pushAt 2514 2 1832,
   opAt 2515 .JUMP]

/-- Instructions 2516..2518, pc 3798..3802: the zero-byte arm. -/
def blk2516 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2516 .JUMPDEST,
   pushAt 2517 2 1789,
   opAt 2518 .JUMP]

/-- Instructions 2519..2526, pc 3803..3820: the direct RR set arm. -/
def blk2519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2519 .JUMPDEST,
   pushAt 2520 2 5120,
   pushAt 2521 2 1615,
   pushAt 2522 2 6144,
   opAt 2523 (.Dup ⟨2, by decide⟩),
   pushAt 2524 2 6144,
   pushAt 2525 2 1939,
   opAt 2526 .JUMP]
end Challenge.Modexp.Submission.Proofs.Fast
