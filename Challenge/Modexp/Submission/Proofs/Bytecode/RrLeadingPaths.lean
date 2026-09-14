import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Located direct RR helper: indices 2511..2533, bytes 3194..3218. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) =
      p.instructionPC base +
        (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem helperPCAnchor :
    Artifact.submissionArtifact.instructionPC 1726 = 2266 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 1726 ≤ i) (hhi : i ≤ 1748) :
    Artifact.submissionArtifact.instructionPC i =
      ([2266,2267,2270,2271,2274,2277,2278,2279,2281,2282,2283,2285,2286,2287,2289,2290,2291,2293,2294,2295,2296,2297,2300] : List Nat)[i - 1726]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1726 .JUMPDEST,
   pushAt 1727 2 2688,
   opAt 1728 .MLOAD,
   pushAt 1729 2 1280,
   pushAt 1730 2 1536,
   opAt 1731 .MCOPY,
   opAt 1732 (.Dup ⟨1, by decide⟩),
   pushAt 1733 1 3,
   opAt 1734 .LT,
   opAt 1735 (.Dup ⟨2, by decide⟩),
   pushAt 1736 1 7,
   opAt 1737 .LT,
   opAt 1738 (.Dup ⟨3, by decide⟩),
   pushAt 1739 1 15,
   opAt 1740 .LT,
   opAt 1741 (.Dup ⟨4, by decide⟩),
   pushAt 1742 1 31,
   opAt 1743 .LT,
   opAt 1744 .ADD,
   opAt 1745 .ADD,
   opAt 1746 .ADD,
   pushAt 1747 2 791,
   opAt 1748 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 791 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
