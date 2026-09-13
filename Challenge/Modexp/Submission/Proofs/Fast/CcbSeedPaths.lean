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
  [opAt 2068 .JUMPDEST,
   pushAt 2069 2 2777,
   opAt 2070 (.Dup ⟨3, by decide⟩),
   opAt 2071 (.Dup ⟨0, by decide⟩),
   opAt 2072 (.Dup ⟨0, by decide⟩),
   pushAt 2073 2 1474,
   opAt 2074 .JUMP]

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2059 .JUMPDEST,
   pushAt 2060 2 2688,
   opAt 2061 .MLOAD,
   pushAt 2062 1 128,
   opAt 2063 .LT,
   opAt 2064 .JUMPDEST,
   pushAt 2065 1 8,
   opAt 2066 (.Dup ⟨1, by decide⟩),
   opAt 2067 .SHL]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2082 .POP,
   pushAt 2083 1 5,
   opAt 2084 .SUB,
   pushAt 2085 2 1634,
   opAt 2086 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2075 .JUMPDEST,
   pushAt 2076 0 0,
   opAt 2077 .NOT,
   opAt 2078 .ADD,
   opAt 2079 (.Dup ⟨0, by decide⟩),
   pushAt 2080 2 2766,
   opAt 2081 .JUMPI]

private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem seedPCAnchor :
    Artifact.submissionArtifact.instructionPC 2059 = 2753 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2059 ≤ i) (hii : i ≤ 2086) :
    Artifact.submissionArtifact.instructionPC i =
      ([2753,2754,2757,2758,2760,2761,2762,2764,2765,2766,2767,2770,2771,2772,2773,2776,2777,2778,2779,2780,2781,2782,2785,2786,2787,2789,2790,2793] : List Nat)[i - 2059]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2753 = true :=
  Artifact.isValidJumpDest_index 2059 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2766 = true :=
  Artifact.isValidJumpDest_index 2068 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2777 = true :=
  Artifact.isValidJumpDest_index 2075 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
