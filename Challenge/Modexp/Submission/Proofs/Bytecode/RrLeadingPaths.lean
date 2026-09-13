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
    Artifact.submissionArtifact.instructionPC 1824 = 2438 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 1824 ≤ i) (hhi : i ≤ 1846) :
    Artifact.submissionArtifact.instructionPC i =
      ([2438,2439,2442,2443,2446,2449,2450,2451,2453,2454,2455,2457,2458,2459,2461,2462,2463,2465,2466,2467,2468,2469,2472] : List Nat)[i - 1824]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1824 .JUMPDEST,
   pushAt 1825 2 2688,
   opAt 1826 .MLOAD,
   pushAt 1827 2 1280,
   pushAt 1828 2 1536,
   opAt 1829 .MCOPY,
   opAt 1830 (.Dup ⟨1, by decide⟩),
   pushAt 1831 1 3,
   opAt 1832 .LT,
   opAt 1833 (.Dup ⟨2, by decide⟩),
   pushAt 1834 1 7,
   opAt 1835 .LT,
   opAt 1836 (.Dup ⟨3, by decide⟩),
   pushAt 1837 1 15,
   opAt 1838 .LT,
   opAt 1839 (.Dup ⟨4, by decide⟩),
   pushAt 1840 1 31,
   opAt 1841 .LT,
   opAt 1842 .ADD,
   opAt 1843 .ADD,
   opAt 1844 .ADD,
   pushAt 1845 2 918,
   opAt 1846 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 918 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
