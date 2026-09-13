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
    Artifact.submissionArtifact.instructionPC 1817 = 2438 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 1817 ≤ i) (hhi : i ≤ 1839) :
    Artifact.submissionArtifact.instructionPC i =
      ([2438,2439,2442,2443,2446,2449,2450,2451,2453,2454,2455,2457,2458,2459,2461,2462,2463,2465,2466,2467,2468,2469,2472] : List Nat)[i - 1817]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1817 .JUMPDEST,
   pushAt 1818 2 2688,
   opAt 1819 .MLOAD,
   pushAt 1820 2 1280,
   pushAt 1821 2 1536,
   opAt 1822 .MCOPY,
   opAt 1823 (.Dup ⟨1, by decide⟩),
   pushAt 1824 1 3,
   opAt 1825 .LT,
   opAt 1826 (.Dup ⟨2, by decide⟩),
   pushAt 1827 1 7,
   opAt 1828 .LT,
   opAt 1829 (.Dup ⟨3, by decide⟩),
   pushAt 1830 1 15,
   opAt 1831 .LT,
   opAt 1832 (.Dup ⟨4, by decide⟩),
   pushAt 1833 1 31,
   opAt 1834 .LT,
   opAt 1835 .ADD,
   opAt 1836 .ADD,
   opAt 1837 .ADD,
   pushAt 1838 2 918,
   opAt 1839 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 918 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
