import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Located direct RR helper: indices 2509..2531, bytes 3243..3267. -/

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
    Artifact.submissionArtifact.instructionPC 2259 = 2970 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2259 ≤ i) (hhi : i ≤ 2281) :
    Artifact.submissionArtifact.instructionPC i =
      ([2970,2971,2974,2975,2978,2981,2982,2983,2985,2986,2987,2989,2990,2991,2993,2994,2995,2997,2998,2999,3000,3001,3004] : List Nat)[i - 2259]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2259 .JUMPDEST,
   pushAt 2260 2 2688,
   opAt 2261 .MLOAD,
   pushAt 2262 2 1280,
   pushAt 2263 2 1536,
   opAt 2264 .MCOPY,
   opAt 2265 (.Dup ⟨1, by decide⟩),
   pushAt 2266 1 3,
   opAt 2267 .LT,
   opAt 2268 (.Dup ⟨2, by decide⟩),
   pushAt 2269 1 7,
   opAt 2270 .LT,
   opAt 2271 (.Dup ⟨3, by decide⟩),
   pushAt 2272 1 15,
   opAt 2273 .LT,
   opAt 2274 (.Dup ⟨4, by decide⟩),
   pushAt 2275 1 31,
   opAt 2276 .LT,
   opAt 2277 .ADD,
   opAt 2278 .ADD,
   opAt 2279 .ADD,
   pushAt 2280 2 1452,
   opAt 2281 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1452 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
