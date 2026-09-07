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
    Artifact.submissionArtifact.instructionPC 2560 = 4016 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2560 ≤ i) (hii : i ≤ 2587) :
    Artifact.submissionArtifact.instructionPC i =
      ([4016,4017,4020,4021,4023,4024,4025,4027,4028,4029,4030,4033,4034,4035,4036,4039,4040,4041,4042,4043,4044,4045,4048,4049,4050,4052,4053,4056] : List Nat)[i - 2560]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2560 .JUMPDEST,
   pushAt 2561 2 9344,
   opAt 2562 .MLOAD,
   pushAt 2563 1 128,
   opAt 2564 .LT,
   opAt 2565 (.Dup ⟨0, by decide⟩),
   pushAt 2566 1 8,
   opAt 2567 (.Swap ⟨0, by decide⟩),
   opAt 2568 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2569 .JUMPDEST,
   pushAt 2570 2 4040,
   opAt 2571 (.Dup ⟨3, by decide⟩),
   opAt 2572 (.Dup ⟨0, by decide⟩),
   opAt 2573 (.Dup ⟨0, by decide⟩),
   pushAt 2574 2 2467,
   opAt 2575 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2576 .JUMPDEST,
   pushAt 2577 0 0,
   opAt 2578 .NOT,
   opAt 2579 .ADD,
   opAt 2580 (.Dup ⟨0, by decide⟩),
   pushAt 2581 2 4029,
   opAt 2582 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 .POP,
   pushAt 2584 1 5,
   opAt 2585 .SUB,
   pushAt 2586 2 2877,
   opAt 2587 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4016 = true :=
  Artifact.isValidJumpDest_index 2560 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4029 = true :=
  Artifact.isValidJumpDest_index 2569 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4040 = true :=
  Artifact.isValidJumpDest_index 2576 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
