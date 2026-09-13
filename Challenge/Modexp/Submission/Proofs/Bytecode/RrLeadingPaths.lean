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
    Artifact.submissionArtifact.instructionPC 1815 = 2395 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 1815 ≤ i) (hhi : i ≤ 1837) :
    Artifact.submissionArtifact.instructionPC i =
      ([2395,2396,2399,2400,2403,2406,2407,2408,2410,2411,2412,2414,2415,2416,2418,2419,2420,2422,2423,2424,2425,2426,2429] : List Nat)[i - 1815]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1815 .JUMPDEST,
   pushAt 1816 2 2688,
   opAt 1817 .MLOAD,
   pushAt 1818 2 1280,
   pushAt 1819 2 1536,
   opAt 1820 .MCOPY,
   opAt 1821 (.Dup ⟨1, by decide⟩),
   pushAt 1822 1 3,
   opAt 1823 .LT,
   opAt 1824 (.Dup ⟨2, by decide⟩),
   pushAt 1825 1 7,
   opAt 1826 .LT,
   opAt 1827 (.Dup ⟨3, by decide⟩),
   pushAt 1828 1 15,
   opAt 1829 .LT,
   opAt 1830 (.Dup ⟨4, by decide⟩),
   pushAt 1831 1 31,
   opAt 1832 .LT,
   opAt 1833 .ADD,
   opAt 1834 .ADD,
   opAt 1835 .ADD,
   pushAt 1836 2 903,
   opAt 1837 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 903 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
