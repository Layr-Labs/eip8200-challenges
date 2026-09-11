import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 17 (instructions 1816..1830).

`RRSEL` (pc 2609) sits between the `RR` chain's selector and its multiply.
The selector is `R1` when the corresponding bit of `n` is clear, and `R1` is
the Montgomery form of one, so that multiply is the identity; this block skips
the call in that case and rejoins at pc 1615 with the stack untouched.

* `blk1816` (idx 1816..1821, pc 2609..2980) — the `selOf = R1` test;
* `blk1822` (idx 1822..1827, pc 2981..2632) — the `MONPRO` call frame;
* `blk1828` (idx 1828..1830, pc 2633..2637) — the skip, straight to pc 1615. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1816..1821, pc 2609..2980. -/
def blk1816 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1702 .JUMPDEST,
   opAt 1703 (.Dup ⟨0, by decide⟩),
   pushAt 1704 2 4096,
   opAt 1705 .EQ,
   pushAt 1706 2 1503,
   opAt 1707 .JUMPI]

/-- Instructions 1822..1827, pc 2981..2632: the multiply's call frame. -/
def blk1822 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1708 2 1503,
   pushAt 1709 2 6144,
   opAt 1710 (.Dup ⟨2, by decide⟩),
   pushAt 1711 2 6144,
   pushAt 1712 2 4049,
   opAt 1713 .JUMP]

/-- Instructions 1828..1830, pc 2633..2637: the skip. -/
def blk1828 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

end Challenge.Modexp.Submission.Proofs.Fast
