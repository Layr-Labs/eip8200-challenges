import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 17 (instructions 1943..1957).

`RRSEL` (pc 2744) sits between the `RR` chain's selector and its multiply.
The selector is `R1` when the corresponding bit of `n` is clear, and `R1` is
the Montgomery form of one, so that multiply is the identity; this block skips
the call in that case and rejoins at pc 1692 with the stack untouched.

* `blk1816` (idx 1943..1948, pc 2744..3189) — the `selOf = R1` test;
* `blk1822` (idx 1952..1952, pc 1824..2767) — the `MONPRO` call frame;
* `blk1828` (idx 1955..1957, pc 2768..2772) — the skip, straight to pc 1692. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1943..1948, pc 2744..3189. -/
def blk1816 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1146 .JUMPDEST,
   opAt 1147 (.Dup ⟨0, by decide⟩),
   pushAt 1148 2 1024,
   opAt 1149 .EQ,
   pushAt 1150 2 826,
   opAt 1151 .JUMPI]

/-- Instructions 1952..1952, pc 1824..2767: the multiply's call frame. -/
def blk1822 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1152 2 826,
   pushAt 1153 2 1536,
   opAt 1154 (.Dup ⟨2, by decide⟩),
   pushAt 1155 2 1536,
   pushAt 1156 2 3353,
   opAt 1157 .JUMP]

/-- Instructions 1955..1957, pc 2768..2772: the skip. -/
def blk1828 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

end Challenge.Modexp.Submission.Proofs.Fast
