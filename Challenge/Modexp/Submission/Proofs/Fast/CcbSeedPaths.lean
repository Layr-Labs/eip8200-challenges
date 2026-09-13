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
  [opAt 2069 .JUMPDEST,
   pushAt 2070 2 2778,
   opAt 2071 (.Dup ⟨3, by decide⟩),
   opAt 2072 (.Dup ⟨0, by decide⟩),
   opAt 2073 (.Dup ⟨0, by decide⟩),
   pushAt 2074 2 1475,
   opAt 2075 .JUMP]

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2060 .JUMPDEST,
   pushAt 2061 2 2688,
   opAt 2062 .MLOAD,
   pushAt 2063 1 128,
   opAt 2064 .LT,
   opAt 2065 (.Dup ⟨0, by decide⟩),
   pushAt 2066 1 8,
   opAt 2067 (.Swap ⟨0, by decide⟩),
   opAt 2068 .SHL]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2083 .POP,
   pushAt 2084 1 5,
   opAt 2085 .SUB,
   pushAt 2086 2 1635,
   opAt 2087 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2076 .JUMPDEST,
   pushAt 2077 0 0,
   opAt 2078 .NOT,
   opAt 2079 .ADD,
   opAt 2080 (.Dup ⟨0, by decide⟩),
   pushAt 2081 2 2767,
   opAt 2082 .JUMPI]

private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem seedPCAnchor :
    Artifact.submissionArtifact.instructionPC 2060 = 2754 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2060 ≤ i) (hii : i ≤ 2087) :
    Artifact.submissionArtifact.instructionPC i =
      ([2754,2755,2758,2759,2761,2762,2763,2765,2766,2767,2768,2771,2772,2773,2774,2777,2778,2779,2780,2781,2782,2783,2786,2787,2788,2790,2791,2794] : List Nat)[i - 2060]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2754 = true :=
  Artifact.isValidJumpDest_index 2060 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2767 = true :=
  Artifact.isValidJumpDest_index 2069 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2778 = true :=
  Artifact.isValidJumpDest_index 2076 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
