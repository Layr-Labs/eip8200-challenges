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
  [opAt 1798 .JUMPDEST,
   opAt 1799 (.Dup ⟨0, by decide⟩),
   pushAt 1800 2 4096,
   opAt 1801 .EQ,
   pushAt 1802 2 1615,
   opAt 1803 .JUMPI]

/-- Instructions 1822..1827, pc 2981..2632: the multiply's call frame. -/
def blk1822 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1804 2 1615,
   pushAt 1805 2 6144,
   opAt 1806 (.Dup ⟨2, by decide⟩),
   pushAt 1807 2 6144,
   pushAt 1808 2 4458,
   opAt 1809 .JUMP]

/-- Instructions 1828..1830, pc 2633..2637: the skip. -/
def blk1828 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1810 .JUMPDEST,
   pushAt 1811 2 1615,
   opAt 1812 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
