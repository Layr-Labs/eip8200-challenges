import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 14 (instructions 1869..1894).

`CCB` (pc 2624) replaces the second `DOUBLE256` call: it doubles `CC` once
through `ADDMOD` and then squares it eight times through `MONPRO`, which
carries `R mod m` to `radix * R mod m` in `8` Montgomery multiplications
instead of `256` modular doublings. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1869..1875, pc 2624..2646: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1878..1884, pc 2560..2660: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 874 .JUMPDEST,
   pushAt 875 2 1266,
   opAt 876 (.Dup ⟨2, by decide⟩),
   opAt 877 (.Dup ⟨0, by decide⟩),
   opAt 878 (.Dup ⟨0, by decide⟩),
   pushAt 879 2 3209,
   opAt 880 .JUMP]

/-- Instructions 1888..1891, pc 2661..2670: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 881 .JUMPDEST,
   pushAt 882 0 0,
   opAt 883 .NOT,
   opAt 884 .ADD,
   opAt 885 (.Dup ⟨0, by decide⟩),
   pushAt 886 2 1255,
   opAt 887 .JUMPI]

/-- Instructions 1892..1894, pc 2671..3035: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 888 .POP,
   opAt 889 .POP,
   opAt 890 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
