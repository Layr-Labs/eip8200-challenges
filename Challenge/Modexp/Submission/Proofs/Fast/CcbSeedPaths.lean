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
  [opAt 2065 .JUMPDEST,
   pushAt 2066 2 2771,
   opAt 2067 (.Dup ⟨3, by decide⟩),
   opAt 2068 (.Dup ⟨0, by decide⟩),
   opAt 2069 (.Dup ⟨0, by decide⟩),
   pushAt 2070 2 1475,
   opAt 2071 .JUMP]

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2056 .JUMPDEST,
   pushAt 2057 2 2688,
   opAt 2058 .MLOAD,
   pushAt 2059 1 128,
   opAt 2060 .LT,
   opAt 2061 (.Dup ⟨0, by decide⟩),
   pushAt 2062 1 8,
   opAt 2063 (.Swap ⟨0, by decide⟩),
   opAt 2064 .SHL]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2079 .POP,
   pushAt 2080 1 5,
   opAt 2081 .SUB,
   pushAt 2082 2 1635,
   opAt 2083 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2072 .JUMPDEST,
   pushAt 2073 0 0,
   opAt 2074 .NOT,
   opAt 2075 .ADD,
   opAt 2076 (.Dup ⟨0, by decide⟩),
   pushAt 2077 2 2760,
   opAt 2078 .JUMPI]

private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem seedPCAnchor :
    Artifact.submissionArtifact.instructionPC 2056 = 2747 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2056 ≤ i) (hii : i ≤ 2083) :
    Artifact.submissionArtifact.instructionPC i =
      ([2747,2748,2751,2752,2754,2755,2756,2758,2759,2760,2761,2764,2765,2766,2767,2770,2771,2772,2773,2774,2775,2776,2779,2780,2781,2783,2784,2787] : List Nat)[i - 2056]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2747 = true :=
  Artifact.isValidJumpDest_index 2056 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2760 = true :=
  Artifact.isValidJumpDest_index 2065 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2771 = true :=
  Artifact.isValidJumpDest_index 2072 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
