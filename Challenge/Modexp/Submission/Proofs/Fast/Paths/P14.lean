import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 14 (instructions 1882..1898).

`CCB` (pc 2624) replaces the second `DOUBLE256` call: it doubles `CC` once
through `ADDMOD` and then squares it eight times through `MONPRO`, which
carries `R mod m` to `radix * R mod m` in `8` Montgomery multiplications
instead of `256` modular doublings. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1882..1874, pc 2624..2641: `CCB` entry, `ADDMOD(px, px) → px`. -/
def blk1742 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- Instructions 1877..1883, pc 2560..2655: `MONPRO(px, px) → px`. -/
def blk1751 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1164 .JUMPDEST,
   pushAt 1165 2 1646,
   opAt 1166 (.Dup ⟨2, by decide⟩),
   opAt 1167 (.Dup ⟨0, by decide⟩),
   opAt 1168 (.Dup ⟨0, by decide⟩),
   pushAt 1169 2 3541,
   opAt 1170 .JUMP]

/-- Instructions 1888..1884, pc 2661..2670: decrement and loop back. -/
def blk1758 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1171 .JUMPDEST,
   pushAt 1172 0 0,
   opAt 1173 .NOT,
   opAt 1174 .ADD,
   opAt 1175 (.Dup ⟨0, by decide⟩),
   pushAt 1176 2 1635,
   opAt 1177 .JUMPI]

/-- Instructions 1896..1898, pc 2671..3030: drop the counter and return. -/
def blk1765 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1178 .POP,
   opAt 1179 .POP,
   opAt 1180 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
