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
    Artifact.submissionArtifact.instructionPC 2329 = 3023 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2329 ≤ i) (hhi : i ≤ 2351) :
    Artifact.submissionArtifact.instructionPC i =
      ([3023,3024,3027,3028,3031,3034,3035,3036,3038,3039,3040,3042,3043,3044,3046,3047,3048,3050,3051,3052,3053,3054,3057] : List Nat)[i - 2329]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2329 .JUMPDEST,
   pushAt 2330 2 9344,
   opAt 2331 .MLOAD,
   pushAt 2332 2 5120,
   pushAt 2333 2 6144,
   opAt 2334 .MCOPY,
   opAt 2335 (.Dup ⟨1, by decide⟩),
   pushAt 2336 1 3,
   opAt 2337 .LT,
   opAt 2338 (.Dup ⟨2, by decide⟩),
   pushAt 2339 1 7,
   opAt 2340 .LT,
   opAt 2341 (.Dup ⟨3, by decide⟩),
   pushAt 2342 1 15,
   opAt 2343 .LT,
   opAt 2344 (.Dup ⟨4, by decide⟩),
   pushAt 2345 1 31,
   opAt 2346 .LT,
   opAt 2347 .ADD,
   opAt 2348 .ADD,
   opAt 2349 .ADD,
   pushAt 2350 2 1467,
   opAt 2351 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1467 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
