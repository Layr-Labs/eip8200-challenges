import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 17 (instructions 1942..1956).

`RRSEL` (pc 2744) sits between the `RR` chain's selector and its multiply.
The selector is `R1` when the corresponding bit of `n` is clear, and `R1` is
the Montgomery form of one, so that multiply is the identity; this block skips
the call in that case and rejoins at pc 1692 with the stack untouched.

* `blk1816` (idx 1942..1947, pc 2744..3184) — the `selOf = R1` test;
* `blk1822` (idx 1952..1952, pc 1824..2767) — the `MONPRO` call frame;
* `blk1828` (idx 1954..1956, pc 2768..2767) — the skip, straight to pc 1692. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1942..1947, pc 2744..3184. -/
def blk1816 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1229 .JUMPDEST,
   opAt 1230 (.Dup ⟨0, by decide⟩),
   pushAt 1231 2 1024,
   opAt 1232 .EQ,
   pushAt 1233 2 936,
   opAt 1234 .JUMPI]

/-- Instructions 1952..1952, pc 1824..2767: the multiply's call frame. -/
def blk1822 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1235 2 936,
   pushAt 1236 2 1536,
   opAt 1237 (.Dup ⟨2, by decide⟩),
   pushAt 1238 2 1536,
   pushAt 1239 2 3541,
   opAt 1240 .JUMP]

/-- Instructions 1954..1956, pc 2768..2767: the skip. -/
def blk1828 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

end Challenge.Modexp.Submission.Proofs.Fast
