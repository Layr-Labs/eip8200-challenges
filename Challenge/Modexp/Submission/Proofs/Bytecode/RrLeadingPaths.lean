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
    Artifact.submissionArtifact.instructionPC 1805 = 2394 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 1805 ≤ i) (hhi : i ≤ 1827) :
    Artifact.submissionArtifact.instructionPC i =
      ([2394,2395,2398,2399,2402,2405,2406,2407,2409,2410,2411,2413,2414,2415,2417,2418,2419,2421,2422,2423,2424,2425,2428] : List Nat)[i - 1805]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1805 .JUMPDEST,
   pushAt 1806 2 2688,
   opAt 1807 .MLOAD,
   pushAt 1808 2 1280,
   pushAt 1809 2 1536,
   opAt 1810 .MCOPY,
   opAt 1811 (.Dup ⟨1, by decide⟩),
   pushAt 1812 1 3,
   opAt 1813 .LT,
   opAt 1814 (.Dup ⟨2, by decide⟩),
   pushAt 1815 1 7,
   opAt 1816 .LT,
   opAt 1817 (.Dup ⟨3, by decide⟩),
   pushAt 1818 1 15,
   opAt 1819 .LT,
   opAt 1820 (.Dup ⟨4, by decide⟩),
   pushAt 1821 1 31,
   opAt 1822 .LT,
   opAt 1823 .ADD,
   opAt 1824 .ADD,
   opAt 1825 .ADD,
   pushAt 1826 2 902,
   opAt 1827 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 902 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
