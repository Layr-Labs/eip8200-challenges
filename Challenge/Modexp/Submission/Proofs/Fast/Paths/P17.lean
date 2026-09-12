import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 17 (instructions 1941..1955).

`RRSEL` (pc 2742) sits between the `RR` chain's selector and its multiply.
The selector is `R1` when the corresponding bit of `n` is clear, and `R1` is
the Montgomery form of one, so that multiply is the identity; this block skips
the call in that case and rejoins at pc 1692 with the stack untouched.

* `blk1816` (idx 1941..1946, pc 2742..3116) — the `selOf = R1` test;
* `blk1822` (idx 1952..1952, pc 3104..2765) — the `MONPRO` call frame;
* `blk1828` (idx 1953..1955, pc 2766..2770) — the skip, straight to pc 1692. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1941..1946, pc 2742..3116. -/
def blk1816 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1670 .JUMPDEST,
   opAt 1671 (.Dup ⟨0, by decide⟩),
   pushAt 1672 2 1024,
   opAt 1673 .EQ,
   pushAt 1674 2 1486,
   opAt 1675 .JUMPI]

/-- Instructions 1952..1952, pc 3104..2765: the multiply's call frame. -/
def blk1822 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1676 2 1486,
   pushAt 1677 2 1536,
   opAt 1678 (.Dup ⟨2, by decide⟩),
   pushAt 1679 2 1536,
   pushAt 1680 2 4141,
   opAt 1681 .JUMP]

/-- Instructions 1953..1955, pc 2766..2770: the skip. -/
def blk1828 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

end Challenge.Modexp.Submission.Proofs.Fast
