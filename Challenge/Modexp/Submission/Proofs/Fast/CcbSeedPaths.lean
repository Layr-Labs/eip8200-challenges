import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CcbSeed

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2058 .JUMPDEST,
   pushAt 2059 2 2776,
   opAt 2060 (.Dup ⟨3, by decide⟩),
   opAt 2061 (.Dup ⟨0, by decide⟩),
   opAt 2062 (.Dup ⟨0, by decide⟩),
   pushAt 2063 2 1475,
   opAt 2064 .JUMP]

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2049 .JUMPDEST,
   pushAt 2050 2 2688,
   opAt 2051 .MLOAD,
   pushAt 2052 1 128,
   opAt 2053 .LT,
   opAt 2054 (.Dup ⟨0, by decide⟩),
   pushAt 2055 1 8,
   opAt 2056 (.Swap ⟨0, by decide⟩),
   opAt 2057 .SHL]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2072 .POP,
   pushAt 2073 1 5,
   opAt 2074 .SUB,
   pushAt 2075 2 1635,
   opAt 2076 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2065 .JUMPDEST,
   pushAt 2066 0 0,
   opAt 2067 .NOT,
   opAt 2068 .ADD,
   opAt 2069 (.Dup ⟨0, by decide⟩),
   pushAt 2070 2 2765,
   opAt 2071 .JUMPI]

private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem seedPCAnchor :
    Artifact.submissionArtifact.instructionPC 2049 = 2752 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2049 ≤ i) (hii : i ≤ 2076) :
    Artifact.submissionArtifact.instructionPC i =
      ([2752,2753,2756,2757,2759,2760,2761,2763,2764,2765,2766,2769,2770,2771,2772,2775,2776,2777,2778,2779,2780,2781,2784,2785,2786,2788,2789,2792] : List Nat)[i - 2049]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2752 = true :=
  Artifact.isValidJumpDest_index 2049 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2765 = true :=
  Artifact.isValidJumpDest_index 2058 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2776 = true :=
  Artifact.isValidJumpDest_index 2065 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
