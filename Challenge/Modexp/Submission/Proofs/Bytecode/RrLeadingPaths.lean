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
    Artifact.submissionArtifact.instructionPC 1730 = 2270 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 1730 ≤ i) (hhi : i ≤ 1752) :
    Artifact.submissionArtifact.instructionPC i =
      ([2270,2271,2274,2275,2278,2281,2282,2283,2285,2286,2287,2289,2290,2291,2293,2294,2295,2297,2298,2299,2300,2301,2304] : List Nat)[i - 1730]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1730 .JUMPDEST,
   pushAt 1731 2 2688,
   opAt 1732 .MLOAD,
   pushAt 1733 2 1280,
   pushAt 1734 2 1536,
   opAt 1735 .MCOPY,
   opAt 1736 (.Dup ⟨1, by decide⟩),
   pushAt 1737 1 3,
   opAt 1738 .LT,
   opAt 1739 (.Dup ⟨2, by decide⟩),
   pushAt 1740 1 7,
   opAt 1741 .LT,
   opAt 1742 (.Dup ⟨3, by decide⟩),
   pushAt 1743 1 15,
   opAt 1744 .LT,
   opAt 1745 (.Dup ⟨4, by decide⟩),
   pushAt 1746 1 31,
   opAt 1747 .LT,
   opAt 1748 .ADD,
   opAt 1749 .ADD,
   opAt 1750 .ADD,
   pushAt 1751 2 793,
   opAt 1752 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 793 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
