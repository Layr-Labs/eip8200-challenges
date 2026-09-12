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
    Artifact.submissionArtifact.instructionPC 2397 = 3128 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2397 ≤ i) (hii : i ≤ 2424) :
    Artifact.submissionArtifact.instructionPC i =
      ([3128,3129,3132,3133,3135,3136,3137,3139,3140,3141,3142,3145,3146,3147,3148,3151,3152,3153,3154,3155,3156,3157,3160,3161,3162,3164,3165,3168] : List Nat)[i - 2397]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2397 .JUMPDEST,
   pushAt 2398 2 9344,
   opAt 2399 .MLOAD,
   pushAt 2400 1 128,
   opAt 2401 .LT,
   opAt 2402 (.Dup ⟨0, by decide⟩),
   pushAt 2403 1 8,
   opAt 2404 (.Swap ⟨0, by decide⟩),
   opAt 2405 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2406 .JUMPDEST,
   pushAt 2407 2 3152,
   opAt 2408 (.Dup ⟨3, by decide⟩),
   opAt 2409 (.Dup ⟨0, by decide⟩),
   opAt 2410 (.Dup ⟨0, by decide⟩),
   pushAt 2411 2 1765,
   opAt 2412 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2413 .JUMPDEST,
   pushAt 2414 0 0,
   opAt 2415 .NOT,
   opAt 2416 .ADD,
   opAt 2417 (.Dup ⟨0, by decide⟩),
   pushAt 2418 2 3141,
   opAt 2419 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2420 .POP,
   pushAt 2421 1 5,
   opAt 2422 .SUB,
   pushAt 2423 2 1925,
   opAt 2424 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3128 = true :=
  Artifact.isValidJumpDest_index 2397 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3141 = true :=
  Artifact.isValidJumpDest_index 2406 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3152 = true :=
  Artifact.isValidJumpDest_index 2413 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
