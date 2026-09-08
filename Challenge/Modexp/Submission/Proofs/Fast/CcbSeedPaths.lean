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
    Artifact.submissionArtifact.instructionPC 2460 = 3978 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2460 ≤ i) (hii : i ≤ 2487) :
    Artifact.submissionArtifact.instructionPC i =
      [3978,3979,3982,3983,3985,3986,3987,3989,3990,3991,3992,3995,3996,3997,3998,4001,4002,4003,4004,4005,4006,4007,4010,4011,4012,4014,4015,4018][i - 2460]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2460 .JUMPDEST,
   pushAt 2461 2 9344,
   opAt 2462 .MLOAD,
   pushAt 2463 1 128,
   opAt 2464 .LT,
   opAt 2465 (.Dup ⟨0, by decide⟩),
   pushAt 2466 1 8,
   opAt 2467 (.Swap ⟨0, by decide⟩),
   opAt 2468 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2469 .JUMPDEST,
   pushAt 2470 2 4002,
   opAt 2471 (.Dup ⟨3, by decide⟩),
   opAt 2472 (.Dup ⟨0, by decide⟩),
   opAt 2473 (.Dup ⟨0, by decide⟩),
   pushAt 2474 2 2437,
   opAt 2475 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2476 .JUMPDEST,
   pushAt 2477 0 0,
   opAt 2478 .NOT,
   opAt 2479 .ADD,
   opAt 2480 (.Dup ⟨0, by decide⟩),
   pushAt 2481 2 3991,
   opAt 2482 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2483 .POP,
   pushAt 2484 1 5,
   opAt 2485 .SUB,
   pushAt 2486 2 2839,
   opAt 2487 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3978 = true :=
  Artifact.isValidJumpDest_index 2460 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3991 = true :=
  Artifact.isValidJumpDest_index 2469 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4002 = true :=
  Artifact.isValidJumpDest_index 2476 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
