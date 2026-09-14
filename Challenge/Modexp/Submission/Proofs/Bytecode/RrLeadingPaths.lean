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
    Artifact.submissionArtifact.instructionPC 1816 = 2394 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 1816 ≤ i) (hhi : i ≤ 1838) :
    Artifact.submissionArtifact.instructionPC i =
      ([2394,2395,2398,2399,2402,2405,2406,2407,2409,2410,2411,2413,2414,2415,2417,2418,2419,2421,2422,2423,2424,2425,2428] : List Nat)[i - 1816]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1816 .JUMPDEST,
   pushAt 1817 2 2688,
   opAt 1818 .MLOAD,
   pushAt 1819 2 1280,
   pushAt 1820 2 1536,
   opAt 1821 .MCOPY,
   opAt 1822 (.Dup ⟨1, by decide⟩),
   pushAt 1823 1 3,
   opAt 1824 .LT,
   opAt 1825 (.Dup ⟨2, by decide⟩),
   pushAt 1826 1 7,
   opAt 1827 .LT,
   opAt 1828 (.Dup ⟨3, by decide⟩),
   pushAt 1829 1 15,
   opAt 1830 .LT,
   opAt 1831 (.Dup ⟨4, by decide⟩),
   pushAt 1832 1 31,
   opAt 1833 .LT,
   opAt 1834 .ADD,
   opAt 1835 .ADD,
   opAt 1836 .ADD,
   pushAt 1837 2 903,
   opAt 1838 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 903 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
