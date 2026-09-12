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
    Artifact.submissionArtifact.instructionPC 2554 = 3396 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2554 ≤ i) (hii : i ≤ 2581) :
    Artifact.submissionArtifact.instructionPC i =
      ([3396,3397,3400,3401,3403,3404,3405,3407,3408,3409,3410,3413,3414,3415,3416,3419,3420,3421,3422,3423,3424,3425,3428,3429,3430,3432,3433,3436] : List Nat)[i - 2554]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2554 .JUMPDEST,
   pushAt 2555 2 5248,
   opAt 2556 .MLOAD,
   pushAt 2557 1 128,
   opAt 2558 .LT,
   opAt 2559 (.Dup ⟨0, by decide⟩),
   pushAt 2560 1 8,
   opAt 2561 (.Swap ⟨0, by decide⟩),
   opAt 2562 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2563 .JUMPDEST,
   pushAt 2564 2 3420,
   opAt 2565 (.Dup ⟨3, by decide⟩),
   opAt 2566 (.Dup ⟨0, by decide⟩),
   opAt 2567 (.Dup ⟨0, by decide⟩),
   pushAt 2568 2 2033,
   opAt 2569 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2570 .JUMPDEST,
   pushAt 2571 0 0,
   opAt 2572 .NOT,
   opAt 2573 .ADD,
   opAt 2574 (.Dup ⟨0, by decide⟩),
   pushAt 2575 2 3409,
   opAt 2576 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2577 .POP,
   pushAt 2578 1 5,
   opAt 2579 .SUB,
   pushAt 2580 2 2193,
   opAt 2581 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3396 = true :=
  Artifact.isValidJumpDest_index 2554 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3409 = true :=
  Artifact.isValidJumpDest_index 2563 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3420 = true :=
  Artifact.isValidJumpDest_index 2570 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
