import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Located direct RR helper: indices 2417..2439, bytes 3152..3181. -/

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
    Artifact.submissionArtifact.instructionPC 2235 = 2878 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2235 ≤ i) (hhi : i ≤ 2257) :
    Artifact.submissionArtifact.instructionPC i =
      ([2878,2879,2882,2883,2886,2889,2890,2891,2893,2894,2895,2897,2898,2899,2901,2902,2903,2905,2906,2907,2908,2909,2912] : List Nat)[i - 2235]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2235 .JUMPDEST,
   pushAt 2236 2 9344,
   opAt 2237 .MLOAD,
   pushAt 2238 2 5120,
   pushAt 2239 2 6144,
   opAt 2240 .MCOPY,
   opAt 2241 (.Dup ⟨1, by decide⟩),
   pushAt 2242 1 3,
   opAt 2243 .LT,
   opAt 2244 (.Dup ⟨2, by decide⟩),
   pushAt 2245 1 7,
   opAt 2246 .LT,
   opAt 2247 (.Dup ⟨3, by decide⟩),
   pushAt 2248 1 15,
   opAt 2249 .LT,
   opAt 2250 (.Dup ⟨4, by decide⟩),
   pushAt 2251 1 31,
   opAt 2252 .LT,
   opAt 2253 .ADD,
   opAt 2254 .ADD,
   opAt 2255 .ADD,
   pushAt 2256 2 1370,
   opAt 2257 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1370 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
