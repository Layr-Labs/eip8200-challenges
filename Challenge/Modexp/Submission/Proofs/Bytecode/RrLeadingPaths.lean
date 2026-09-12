import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Located direct RR helper: indices 2514..2536, bytes 3248..3277. -/

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
    Artifact.submissionArtifact.instructionPC 2262 = 2975 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2262 ≤ i) (hhi : i ≤ 2284) :
    Artifact.submissionArtifact.instructionPC i =
      ([2975,2976,2979,2980,2983,2986,2987,2988,2990,2991,2992,2994,2995,2996,2998,2999,3000,3002,3003,3004,3005,3006,3009] : List Nat)[i - 2262]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2262 .JUMPDEST,
   pushAt 2263 2 5248,
   opAt 2264 .MLOAD,
   pushAt 2265 2 1280,
   pushAt 2266 2 1536,
   opAt 2267 .MCOPY,
   opAt 2268 (.Dup ⟨1, by decide⟩),
   pushAt 2269 1 3,
   opAt 2270 .LT,
   opAt 2271 (.Dup ⟨2, by decide⟩),
   pushAt 2272 1 7,
   opAt 2273 .LT,
   opAt 2274 (.Dup ⟨3, by decide⟩),
   pushAt 2275 1 15,
   opAt 2276 .LT,
   opAt 2277 (.Dup ⟨4, by decide⟩),
   pushAt 2278 1 31,
   opAt 2279 .LT,
   opAt 2280 .ADD,
   opAt 2281 .ADD,
   opAt 2282 .ADD,
   pushAt 2283 2 1452,
   opAt 2284 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1452 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
