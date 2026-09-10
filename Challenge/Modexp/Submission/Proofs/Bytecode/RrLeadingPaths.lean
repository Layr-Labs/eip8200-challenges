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
    Artifact.submissionArtifact.instructionPC 2376 = 3111 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2376 ≤ i) (hhi : i ≤ 2398) :
    Artifact.submissionArtifact.instructionPC i =
      ([3111,3112,3115,3116,3119,3122,3123,3124,3126,3127,3128,3130,3131,3132,3134,3135,3136,3138,3139,3140,3141,3142,3145] : List Nat)[i - 2376]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2376 .JUMPDEST,
   pushAt 2377 2 9344,
   opAt 2378 .MLOAD,
   pushAt 2379 2 5120,
   pushAt 2380 2 6144,
   opAt 2381 .MCOPY,
   opAt 2382 (.Dup ⟨1, by decide⟩),
   pushAt 2383 1 3,
   opAt 2384 .LT,
   opAt 2385 (.Dup ⟨2, by decide⟩),
   pushAt 2386 1 7,
   opAt 2387 .LT,
   opAt 2388 (.Dup ⟨3, by decide⟩),
   pushAt 2389 1 15,
   opAt 2390 .LT,
   opAt 2391 (.Dup ⟨4, by decide⟩),
   pushAt 2392 1 31,
   opAt 2393 .LT,
   opAt 2394 .ADD,
   opAt 2395 .ADD,
   opAt 2396 .ADD,
   pushAt 2397 2 1548,
   opAt 2398 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1548 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
