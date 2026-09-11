import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc3412 and bypasses the protected island via3423.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2554 ≤ i) (hii : i ≤ 2593) :
    Artifact.submissionArtifact.instructionPC i =
      ([3324,3325,3326,3329,3330,3331,3334,3335,3336,3338,3339,3342,3343,3344,3346,3347,3350,3351,3354,3355,3356,3357,3358,3360,3361,3364,3365,3367,3370,3371,3372,3375,3376,3377,3379,3380,3384,3385,3388,3389] : List Nat)[i - 2554]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2594 ≤ i) (hii : i ≤ 2626) :
    Artifact.submissionArtifact.instructionPC i =
      ([3391,3392,3393,3396,3399,3402,3405,3408,3409,3410,3412,3413,3414,3415,3418,3419,3420,3423,3426,3429,3432,3435,3436,3437,3440,3441,3442,3443,3446,3449,3450,3451,3454] : List Nat)[i - 2594]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2554 .JUMPDEST,
   opAt 2555 (.Dup ⟨3, by decide⟩),
   pushAt 2556 2 3335,
   opAt 2557 .JUMP,
   opAt 2561 .JUMPDEST,
   pushAt 2562 1 3,
   opAt 2563 .EQ,
   pushAt 2564 2 3371,
   opAt 2565 .JUMPI]

def oneWidth : List Located :=
  [opAt 2566 (.Dup ⟨3, by decide⟩),
   pushAt 2567 1 1,
   opAt 2568 .XOR,
   pushAt 2569 2 3441,
   opAt 2570 .JUMPI]

def checkThree : List Located :=
  [pushAt 2571 2 9472,
   opAt 2572 .MLOAD,
   opAt 2573 .CALLDATALOAD,
   pushAt 2574 0 0,
   opAt 2575 .BYTE,
   pushAt 2576 1 3,
   opAt 2577 .XOR,
   pushAt 2578 2 3441,
   opAt 2579 .JUMPI]

def threeHit : List Located :=
  [pushAt 2580 1 1,
   pushAt 2581 2 3392,
   opAt 2582 .JUMP]

def check65537 : List Located :=
  [opAt 2583 .JUMPDEST,
   pushAt 2584 2 9472,
   opAt 2585 .MLOAD,
   opAt 2586 .CALLDATALOAD,
   pushAt 2587 1 232,
   opAt 2588 .SHR,
   pushAt 2589 3 65537,
   opAt 2590 .XOR,
   pushAt 2591 2 3441,
   opAt 2592 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2593 1 16, opAt 2594 .JUMPDEST]

def start : List Located :=
  []

def squareCall : List Located :=
  [opAt 2595 .JUMPDEST,
   pushAt 2596 2 3409,
   pushAt 2597 2 2048,
   pushAt 2598 2 2048,
   pushAt 2599 2 2048,
   pushAt 2600 2 4053,
   opAt 2601 .JUMP]

def squareReturn : List Located :=
  [opAt 2602 .JUMPDEST,
   pushAt 2603 1 1,
   opAt 2604 (.Swap ⟨0, by decide⟩),
   opAt 2605 .SUB,
   opAt 2606 (.Dup ⟨0, by decide⟩),
   pushAt 2607 2 3392,
   opAt 2608 .JUMPI]

def product : List Located :=
  [opAt 2609 .POP,
   pushAt 2610 2 3436,
   pushAt 2611 2 1024,
   pushAt 2612 2 1024,
   pushAt 2613 2 2048,
   pushAt 2614 2 4053,
   opAt 2615 .JUMP]

def finish : List Located :=
  [opAt 2616 .JUMPDEST,
   pushAt 2617 2 1721,
   opAt 2618 .JUMP]

def fallback : List Located :=
  [opAt 2619 .JUMPDEST,
   opAt 2620 (.Dup ⟨0, by decide⟩),
   pushAt 2621 2 4096,
   pushAt 2622 2 1024,
   opAt 2623 .MCOPY,
   pushAt 2624 0 0,
   pushAt 2625 2 1622,
   opAt 2626 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3324 = true :=
  Artifact.isValidJumpDest_index 2554 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3371 = true :=
  Artifact.isValidJumpDest_index 2583 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3391 = true :=
  Artifact.isValidJumpDest_index 2594 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3392 = true :=
  Artifact.isValidJumpDest_index 2595 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3409 = true :=
  Artifact.isValidJumpDest_index 2602 (by rfl)

theorem jumpDest3954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3436 = true :=
  Artifact.isValidJumpDest_index 2616 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3441 = true :=
  Artifact.isValidJumpDest_index 2619 (by rfl)

/-- Actual bypass target around the protected word-path island. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3335 = true :=
  Artifact.isValidJumpDest_index 2561 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
