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
    Artifact.submissionArtifact.instructionPC 2555 = 3392 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2555 ≤ i) (hii : i ≤ 2582) :
    Artifact.submissionArtifact.instructionPC i =
      ([3392,3393,3396,3397,3399,3400,3401,3403,3404,3405,3406,3409,3410,3411,3412,3415,3416,3417,3418,3419,3420,3421,3424,3425,3426,3428,3429,3432] : List Nat)[i - 2555]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2555 .JUMPDEST,
   pushAt 2556 2 5248,
   opAt 2557 .MLOAD,
   pushAt 2558 1 128,
   opAt 2559 .LT,
   opAt 2560 (.Dup ⟨0, by decide⟩),
   pushAt 2561 1 8,
   opAt 2562 (.Swap ⟨0, by decide⟩),
   opAt 2563 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2564 .JUMPDEST,
   pushAt 2565 2 3416,
   opAt 2566 (.Dup ⟨3, by decide⟩),
   opAt 2567 (.Dup ⟨0, by decide⟩),
   opAt 2568 (.Dup ⟨0, by decide⟩),
   pushAt 2569 2 2028,
   opAt 2570 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2571 .JUMPDEST,
   pushAt 2572 0 0,
   opAt 2573 .NOT,
   opAt 2574 .ADD,
   opAt 2575 (.Dup ⟨0, by decide⟩),
   pushAt 2576 2 3405,
   opAt 2577 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 .POP,
   pushAt 2579 1 5,
   opAt 2580 .SUB,
   pushAt 2581 2 2188,
   opAt 2582 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3392 = true :=
  Artifact.isValidJumpDest_index 2555 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3405 = true :=
  Artifact.isValidJumpDest_index 2564 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3416 = true :=
  Artifact.isValidJumpDest_index 2571 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
