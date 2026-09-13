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
  [opAt 1162 .JUMPDEST,
   pushAt 1163 2 1645,
   opAt 1164 (.Dup ⟨2, by decide⟩),
   opAt 1165 (.Dup ⟨0, by decide⟩),
   opAt 1166 (.Dup ⟨0, by decide⟩),
   pushAt 1167 2 3549,
   opAt 1168 .JUMP]

/-- Instructions 1888..1891, pc 2661..2670: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1169 .JUMPDEST,
   pushAt 1170 0 0,
   opAt 1171 .NOT,
   opAt 1172 .ADD,
   opAt 1173 (.Dup ⟨0, by decide⟩),
   pushAt 1174 2 1634,
   opAt 1175 .JUMPI]

/-- Instructions 1892..1894, pc 2671..3035: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1176 .POP,
   opAt 1177 .POP,
   opAt 1178 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
