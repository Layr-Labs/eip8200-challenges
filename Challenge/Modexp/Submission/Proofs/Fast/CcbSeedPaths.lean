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
    Artifact.submissionArtifact.instructionPC 2549 = 3382 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2549 ≤ i) (hii : i ≤ 2576) :
    Artifact.submissionArtifact.instructionPC i =
      ([3382,3383,3386,3387,3389,3390,3391,3393,3394,3395,3396,3399,3400,3401,3402,3405,3406,3407,3408,3409,3410,3411,3414,3415,3416,3418,3419,3422] : List Nat)[i - 2549]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2549 .JUMPDEST,
   pushAt 2550 2 2688,
   opAt 2551 .MLOAD,
   pushAt 2552 1 128,
   opAt 2553 .LT,
   opAt 2554 (.Dup ⟨0, by decide⟩),
   pushAt 2555 1 8,
   opAt 2556 (.Swap ⟨0, by decide⟩),
   opAt 2557 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2558 .JUMPDEST,
   pushAt 2559 2 3406,
   opAt 2560 (.Dup ⟨3, by decide⟩),
   opAt 2561 (.Dup ⟨0, by decide⟩),
   opAt 2562 (.Dup ⟨0, by decide⟩),
   pushAt 2563 2 2023,
   opAt 2564 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2565 .JUMPDEST,
   pushAt 2566 0 0,
   opAt 2567 .NOT,
   opAt 2568 .ADD,
   opAt 2569 (.Dup ⟨0, by decide⟩),
   pushAt 2570 2 3395,
   opAt 2571 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2572 .POP,
   pushAt 2573 1 5,
   opAt 2574 .SUB,
   pushAt 2575 2 2183,
   opAt 2576 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3382 = true :=
  Artifact.isValidJumpDest_index 2549 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3395 = true :=
  Artifact.isValidJumpDest_index 2558 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3406 = true :=
  Artifact.isValidJumpDest_index 2565 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
