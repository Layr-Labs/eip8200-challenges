import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Located direct RR helper: indices 2376..2398, bytes 3111..3145. -/

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
    Artifact.submissionArtifact.instructionPC 2327 = 3023 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2327 ≤ i) (hhi : i ≤ 2349) :
    Artifact.submissionArtifact.instructionPC i =
      ([3023,3024,3027,3028,3031,3034,3035,3036,3038,3039,3040,3042,3043,3044,3046,3047,3048,3050,3051,3052,3053,3054,3057] : List Nat)[i - 2327]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2327 .JUMPDEST,
   pushAt 2328 2 9344,
   opAt 2329 .MLOAD,
   pushAt 2330 2 5120,
   pushAt 2331 2 6144,
   opAt 2332 .MCOPY,
   opAt 2333 (.Dup ⟨1, by decide⟩),
   pushAt 2334 1 3,
   opAt 2335 .LT,
   opAt 2336 (.Dup ⟨2, by decide⟩),
   pushAt 2337 1 7,
   opAt 2338 .LT,
   opAt 2339 (.Dup ⟨3, by decide⟩),
   pushAt 2340 1 15,
   opAt 2341 .LT,
   opAt 2342 (.Dup ⟨4, by decide⟩),
   pushAt 2343 1 31,
   opAt 2344 .LT,
   opAt 2345 .ADD,
   opAt 2346 .ADD,
   opAt 2347 .ADD,
   pushAt 2348 2 1467,
   opAt 2349 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1467 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
