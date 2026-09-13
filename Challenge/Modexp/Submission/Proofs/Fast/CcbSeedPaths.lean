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
    Artifact.submissionArtifact.instructionPC 2063 = 2792 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2063 ≤ i) (hii : i ≤ 2090) :
    Artifact.submissionArtifact.instructionPC i =
      ([2792,2793,2796,2797,2799,2800,2801,2803,2804,2805,2806,2809,2810,2811,2812,2815,2816,2817,2818,2819,2820,2821,2824,2825,2826,2828,2829,2832] : List Nat)[i - 2063]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2063 .JUMPDEST,
   pushAt 2064 2 2688,
   opAt 2065 .MLOAD,
   pushAt 2066 1 128,
   opAt 2067 .LT,
   opAt 2068 (.Dup ⟨0, by decide⟩),
   pushAt 2069 1 8,
   opAt 2070 (.Swap ⟨0, by decide⟩),
   opAt 2071 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2072 .JUMPDEST,
   pushAt 2073 2 2816,
   opAt 2074 (.Dup ⟨3, by decide⟩),
   opAt 2075 (.Dup ⟨0, by decide⟩),
   opAt 2076 (.Dup ⟨0, by decide⟩),
   pushAt 2077 2 1487,
   opAt 2078 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2079 .JUMPDEST,
   pushAt 2080 0 0,
   opAt 2081 .NOT,
   opAt 2082 .ADD,
   opAt 2083 (.Dup ⟨0, by decide⟩),
   pushAt 2084 2 2805,
   opAt 2085 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2086 .POP,
   pushAt 2087 1 5,
   opAt 2088 .SUB,
   pushAt 2089 2 1647,
   opAt 2090 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2792 = true :=
  Artifact.isValidJumpDest_index 2063 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2805 = true :=
  Artifact.isValidJumpDest_index 2072 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2816 = true :=
  Artifact.isValidJumpDest_index 2079 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
