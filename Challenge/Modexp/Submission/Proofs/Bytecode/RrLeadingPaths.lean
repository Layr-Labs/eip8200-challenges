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
    Artifact.submissionArtifact.instructionPC 1811 = 2395 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 1811 ≤ i) (hhi : i ≤ 1833) :
    Artifact.submissionArtifact.instructionPC i =
      ([2395,2396,2399,2400,2403,2406,2407,2408,2410,2411,2412,2414,2415,2416,2418,2419,2420,2422,2423,2424,2425,2426,2429] : List Nat)[i - 1811]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1811 .JUMPDEST,
   pushAt 1812 2 2688,
   opAt 1813 .MLOAD,
   pushAt 1814 2 1280,
   pushAt 1815 2 1536,
   opAt 1816 .MCOPY,
   opAt 1817 (.Dup ⟨1, by decide⟩),
   pushAt 1818 1 3,
   opAt 1819 .LT,
   opAt 1820 (.Dup ⟨2, by decide⟩),
   pushAt 1821 1 7,
   opAt 1822 .LT,
   opAt 1823 (.Dup ⟨3, by decide⟩),
   pushAt 1824 1 15,
   opAt 1825 .LT,
   opAt 1826 (.Dup ⟨4, by decide⟩),
   pushAt 1827 1 31,
   opAt 1828 .LT,
   opAt 1829 .ADD,
   opAt 1830 .ADD,
   opAt 1831 .ADD,
   pushAt 1832 2 903,
   opAt 1833 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 903 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
