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
    Artifact.submissionArtifact.instructionPC 1728 = 2270 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 1728 ≤ i) (hhi : i ≤ 1750) :
    Artifact.submissionArtifact.instructionPC i =
      ([2270,2271,2274,2275,2278,2281,2282,2283,2285,2286,2287,2289,2290,2291,2293,2294,2295,2297,2298,2299,2300,2301,2304] : List Nat)[i - 1728]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1728 .JUMPDEST,
   pushAt 1729 2 2688,
   opAt 1730 .MLOAD,
   pushAt 1731 2 1280,
   pushAt 1732 2 1536,
   opAt 1733 .MCOPY,
   opAt 1734 (.Dup ⟨1, by decide⟩),
   pushAt 1735 1 3,
   opAt 1736 .LT,
   opAt 1737 (.Dup ⟨2, by decide⟩),
   pushAt 1738 1 7,
   opAt 1739 .LT,
   opAt 1740 (.Dup ⟨3, by decide⟩),
   pushAt 1741 1 15,
   opAt 1742 .LT,
   opAt 1743 (.Dup ⟨4, by decide⟩),
   pushAt 1744 1 31,
   opAt 1745 .LT,
   opAt 1746 .ADD,
   opAt 1747 .ADD,
   opAt 1748 .ADD,
   pushAt 1749 2 793,
   opAt 1750 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 793 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
