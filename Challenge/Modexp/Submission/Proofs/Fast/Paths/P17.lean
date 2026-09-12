import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 17 (instructions 1946..1960).

`RRSEL` (pc 2747) sits between the `RR` chain's selector and its multiply.
The selector is `R1` when the corresponding bit of `n` is clear, and `R1` is
the Montgomery form of one, so that multiply is the identity; this block skips
the call in that case and rejoins at pc 1697 with the stack untouched.

* `blk1816` (idx 1946..1951, pc 2747..3121) — the `selOf = R1` test;
* `blk1822` (idx 1952..1957, pc 3104..2770) — the `MONPRO` call frame;
* `blk1828` (idx 1958..1960, pc 2771..2775) — the skip, straight to pc 1697. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1946..1951, pc 2747..3121. -/
def blk1816 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1673 .JUMPDEST,
   opAt 1674 (.Dup ⟨0, by decide⟩),
   pushAt 1675 2 1024,
   opAt 1676 .EQ,
   pushAt 1677 2 1486,
   opAt 1678 .JUMPI]

/-- Instructions 1952..1957, pc 3104..2770: the multiply's call frame. -/
def blk1822 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1679 2 1486,
   pushAt 1680 2 1536,
   opAt 1681 (.Dup ⟨2, by decide⟩),
   pushAt 1682 2 1536,
   pushAt 1683 2 4151,
   opAt 1684 .JUMP]

/-- Instructions 1958..1960, pc 2771..2775: the skip. -/
def blk1828 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

end Challenge.Modexp.Submission.Proofs.Fast
