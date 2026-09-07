import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 17 (instructions 1847..1861).

`RRSEL` (pc 3015) sits between the `RR` chain's selector and its multiply.
The selector is `R1` when the corresponding bit of `n` is clear, and `R1` is
the Montgomery form of one, so that multiply is the identity; this block skips
the call in that case and rejoins at pc 1615 with the stack untouched.

* `blk1816` (idx 1847..1852, pc 3015..3024) — the `selOf = R1` test;
* `blk1822` (idx 1853..1858, pc 3025..3038) — the `MONPRO` call frame;
* `blk1828` (idx 1859..1861, pc 3039..3043) — the skip, straight to pc 1615. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Original block `1816`, now instructions 1847..1852, pc 3015..3024. -/
def blk1816 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1847 .JUMPDEST,
   opAt 1848 (.Dup ⟨0, by decide⟩),
   pushAt 1849 2 4096,
   opAt 1850 .EQ,
   pushAt 1851 2 1615,
   opAt 1852 .JUMPI]

/-- Original block `1822`, now instructions 1853..1858, pc 3025..3038: the multiply's call frame. -/
def blk1822 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1853 2 1615,
   pushAt 1854 2 6144,
   opAt 1855 (.Dup ⟨2, by decide⟩),
   pushAt 1856 2 6144,
   pushAt 1857 2 1939,
   opAt 1858 .JUMP]

/-- Original block `1828`, now instructions 1859..1861, pc 3039..3043: the skip. -/
def blk1828 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1859 .JUMPDEST,
   pushAt 1860 2 1615,
   opAt 1861 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
