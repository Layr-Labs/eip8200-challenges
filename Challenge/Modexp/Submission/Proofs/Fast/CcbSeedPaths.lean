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
    Artifact.submissionArtifact.instructionPC 2555 = 4016 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2555 ≤ i) (hii : i ≤ 2582) :
    Artifact.submissionArtifact.instructionPC i =
      ([4016,4017,4020,4021,4023,4024,4025,4027,4028,4029,4030,4033,4034,4035,4036,4039,4040,4041,4042,4043,4044,4045,4048,4049,4050,4052,4053,4056] : List Nat)[i - 2555]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2555 .JUMPDEST,
   pushAt 2556 2 9344,
   opAt 2557 .MLOAD,
   pushAt 2558 1 128,
   opAt 2559 .LT,
   opAt 2560 (.Dup ⟨0, by decide⟩),
   pushAt 2561 1 8,
   opAt 2562 (.Swap ⟨0, by decide⟩),
   opAt 2563 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2564 .JUMPDEST,
   pushAt 2565 2 4040,
   opAt 2566 (.Dup ⟨3, by decide⟩),
   opAt 2567 (.Dup ⟨0, by decide⟩),
   opAt 2568 (.Dup ⟨0, by decide⟩),
   pushAt 2569 2 2467,
   opAt 2570 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2571 .JUMPDEST,
   pushAt 2572 0 0,
   opAt 2573 .NOT,
   opAt 2574 .ADD,
   opAt 2575 (.Dup ⟨0, by decide⟩),
   pushAt 2576 2 4029,
   opAt 2577 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 .POP,
   pushAt 2579 1 5,
   opAt 2580 .SUB,
   pushAt 2581 2 2877,
   opAt 2582 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4016 = true :=
  Artifact.isValidJumpDest_index 2555 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4029 = true :=
  Artifact.isValidJumpDest_index 2564 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4040 = true :=
  Artifact.isValidJumpDest_index 2571 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
