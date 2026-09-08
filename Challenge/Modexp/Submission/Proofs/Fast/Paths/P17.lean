import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 17 (instructions 1816..1830).

`RRSEL` (pc 2971) sits between the `RR` chain's selector and its multiply.
The selector is `R1` when the corresponding bit of `n` is clear, and `R1` is
the Montgomery form of one, so that multiply is the identity; this block skips
the call in that case and rejoins at pc 1615 with the stack untouched.

* `blk1816` (idx 1816..1821, pc 2971..2980) — the `selOf = R1` test;
* `blk1822` (idx 1822..1827, pc 2981..2994) — the `MONPRO` call frame;
* `blk1828` (idx 1828..1830, pc 2995..2999) — the skip, straight to pc 1615. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1816..1821, pc 2971..2980. -/
def blk1816 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1779 .JUMPDEST,
   opAt 1780 (.Dup ⟨0, by decide⟩),
   pushAt 1781 2 4096,
   opAt 1782 .EQ,
   pushAt 1783 2 1596,
   opAt 1784 .JUMPI]

/-- Instructions 1822..1827, pc 2981..2994: the multiply's call frame. -/
def blk1822 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1785 2 1596,
   pushAt 1786 2 6144,
   opAt 1787 (.Dup ⟨2, by decide⟩),
   pushAt 1788 2 6144,
   pushAt 1789 2 1908,
   opAt 1790 .JUMP]

/-- Instructions 1828..1830, pc 2995..2999: the skip. -/
def blk1828 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1791 .JUMPDEST,
   pushAt 1792 2 1596,
   opAt 1793 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
