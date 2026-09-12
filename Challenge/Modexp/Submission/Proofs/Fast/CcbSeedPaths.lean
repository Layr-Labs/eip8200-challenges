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
    Artifact.submissionArtifact.instructionPC 2566 = 3378 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2566 ≤ i) (hii : i ≤ 2593) :
    Artifact.submissionArtifact.instructionPC i =
      ([3378,3379,3382,3383,3385,3386,3387,3389,3390,3391,3392,3395,3396,3397,3398,3401,3402,3403,3404,3405,3406,3407,3410,3411,3412,3414,3415,3418] : List Nat)[i - 2566]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2566 .JUMPDEST,
   pushAt 2567 2 5248,
   opAt 2568 .MLOAD,
   pushAt 2569 1 128,
   opAt 2570 .LT,
   opAt 2571 (.Dup ⟨0, by decide⟩),
   pushAt 2572 1 8,
   opAt 2573 (.Swap ⟨0, by decide⟩),
   opAt 2574 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2575 .JUMPDEST,
   pushAt 2576 2 3402,
   opAt 2577 (.Dup ⟨3, by decide⟩),
   opAt 2578 (.Dup ⟨0, by decide⟩),
   opAt 2579 (.Dup ⟨0, by decide⟩),
   pushAt 2580 2 2028,
   opAt 2581 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   pushAt 2583 0 0,
   opAt 2584 .NOT,
   opAt 2585 .ADD,
   opAt 2586 (.Dup ⟨0, by decide⟩),
   pushAt 2587 2 3391,
   opAt 2588 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2589 .POP,
   pushAt 2590 1 5,
   opAt 2591 .SUB,
   pushAt 2592 2 2188,
   opAt 2593 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3378 = true :=
  Artifact.isValidJumpDest_index 2566 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3391 = true :=
  Artifact.isValidJumpDest_index 2575 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3402 = true :=
  Artifact.isValidJumpDest_index 2582 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
