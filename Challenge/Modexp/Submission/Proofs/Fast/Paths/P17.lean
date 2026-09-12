import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 17 (instructions 1864..1878).

`RRSEL` (pc 2650) sits between the `RR` chain's selector and its multiply.
The selector is `R1` when the corresponding bit of `n` is clear, and `R1` is
the Montgomery form of one, so that multiply is the identity; this block skips
the call in that case and rejoins at pc 1615 with the stack untouched.

* `blk1816` (idx 1864..1869, pc 2650..3025) — the `selOf = R1` test;
* `blk1822` (idx 1870..1875, pc 3022..2673) — the `MONPRO` call frame;
* `blk1828` (idx 1876..1878, pc 2674..2678) — the skip, straight to pc 1615. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1864..1869, pc 2650..3025. -/
def blk1816 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1635 .JUMPDEST,
   opAt 1636 (.Dup ⟨0, by decide⟩),
   pushAt 1637 2 4096,
   opAt 1638 .EQ,
   pushAt 1639 2 1404,
   opAt 1640 .JUMPI]

/-- Instructions 1870..1875, pc 3022..2673: the multiply's call frame. -/
def blk1822 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1641 2 1404,
   pushAt 1642 2 6144,
   opAt 1643 (.Dup ⟨2, by decide⟩),
   pushAt 1644 2 6144,
   pushAt 1645 2 4055,
   opAt 1646 .JUMP]

/-- Instructions 1876..1878, pc 2674..2678: the skip. -/
def blk1828 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

end Challenge.Modexp.Submission.Proofs.Fast
