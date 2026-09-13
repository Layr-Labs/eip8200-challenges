import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CcbSeed

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem seedPCAnchor :
    Artifact.submissionArtifact.instructionPC 2070 = 2799 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2070 ≤ i) (hii : i ≤ 2097) :
    Artifact.submissionArtifact.instructionPC i =
      ([2799,2800,2803,2804,2806,2807,2808,2810,2811,2812,2813,2816,2817,2818,2819,2822,2823,2824,2825,2826,2827,2828,2831,2832,2833,2835,2836,2839] : List Nat)[i - 2070]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2070 .JUMPDEST,
   pushAt 2071 2 2688,
   opAt 2072 .MLOAD,
   pushAt 2073 1 128,
   opAt 2074 .LT,
   opAt 2075 (.Dup ⟨0, by decide⟩),
   pushAt 2076 1 8,
   opAt 2077 (.Swap ⟨0, by decide⟩),
   opAt 2078 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2079 .JUMPDEST,
   pushAt 2080 2 2823,
   opAt 2081 (.Dup ⟨3, by decide⟩),
   opAt 2082 (.Dup ⟨0, by decide⟩),
   opAt 2083 (.Dup ⟨0, by decide⟩),
   pushAt 2084 2 1491,
   opAt 2085 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2086 .JUMPDEST,
   pushAt 2087 0 0,
   opAt 2088 .NOT,
   opAt 2089 .ADD,
   opAt 2090 (.Dup ⟨0, by decide⟩),
   pushAt 2091 2 2812,
   opAt 2092 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2093 .POP,
   pushAt 2094 1 5,
   opAt 2095 .SUB,
   pushAt 2096 2 1651,
   opAt 2097 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2799 = true :=
  Artifact.isValidJumpDest_index 2070 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2812 = true :=
  Artifact.isValidJumpDest_index 2079 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2823 = true :=
  Artifact.isValidJumpDest_index 2086 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
