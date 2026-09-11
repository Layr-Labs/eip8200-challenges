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

@[simp] theorem directPC0 (i : Nat) (hi : 2556 ≤ i) (hii : i ≤ 2595) :
    Artifact.submissionArtifact.instructionPC i =
      ([3324,3325,3326,3329,3330,3331,3334,3335,3336,3338,3339,3342,3343,3344,3346,3347,3350,3351,3354,3355,3356,3357,3358,3360,3361,3364,3365,3367,3370,3371,3372,3375,3376,3377,3379,3380,3384,3385,3388,3389] : List Nat)[i - 2556]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2596 ≤ i) (hii : i ≤ 2628) :
    Artifact.submissionArtifact.instructionPC i =
      ([3391,3392,3393,3396,3399,3402,3405,3408,3409,3410,3412,3413,3414,3415,3418,3419,3420,3423,3426,3429,3432,3435,3436,3437,3440,3441,3442,3443,3446,3449,3450,3451,3454] : List Nat)[i - 2596]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2556 .JUMPDEST,
   opAt 2557 (.Dup ⟨3, by decide⟩),
   pushAt 2558 2 3335,
   opAt 2559 .JUMP,
   opAt 2563 .JUMPDEST,
   pushAt 2564 1 3,
   opAt 2565 .EQ,
   pushAt 2566 2 3371,
   opAt 2567 .JUMPI]

def oneWidth : List Located :=
  [opAt 2568 (.Dup ⟨3, by decide⟩),
   pushAt 2569 1 1,
   opAt 2570 .XOR,
   pushAt 2571 2 3441,
   opAt 2572 .JUMPI]

def checkThree : List Located :=
  [pushAt 2573 2 9472,
   opAt 2574 .MLOAD,
   opAt 2575 .CALLDATALOAD,
   pushAt 2576 0 0,
   opAt 2577 .BYTE,
   pushAt 2578 1 3,
   opAt 2579 .XOR,
   pushAt 2580 2 3441,
   opAt 2581 .JUMPI]

def threeHit : List Located :=
  [pushAt 2582 1 1,
   pushAt 2583 2 3391,
   opAt 2584 .JUMP]

def check65537 : List Located :=
  [opAt 2585 .JUMPDEST,
   pushAt 2586 2 9472,
   opAt 2587 .MLOAD,
   opAt 2588 .CALLDATALOAD,
   pushAt 2589 1 232,
   opAt 2590 .SHR,
   pushAt 2591 3 65537,
   opAt 2592 .XOR,
   pushAt 2593 2 3441,
   opAt 2594 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2595 1 16]

def start : List Located :=
  [opAt 2596 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2597 .JUMPDEST,
   pushAt 2598 2 3409,
   pushAt 2599 2 2048,
   pushAt 2600 2 2048,
   pushAt 2601 2 2048,
   pushAt 2602 2 4049,
   opAt 2603 .JUMP]

def squareReturn : List Located :=
  [opAt 2604 .JUMPDEST,
   pushAt 2605 1 1,
   opAt 2606 (.Swap ⟨0, by decide⟩),
   opAt 2607 .SUB,
   opAt 2608 (.Dup ⟨0, by decide⟩),
   pushAt 2609 2 3392,
   opAt 2610 .JUMPI]

def product : List Located :=
  [opAt 2611 .POP,
   pushAt 2612 2 3436,
   pushAt 2613 2 1024,
   pushAt 2614 2 1024,
   pushAt 2615 2 2048,
   pushAt 2616 2 4049,
   opAt 2617 .JUMP]

def finish : List Located :=
  [opAt 2618 .JUMPDEST,
   pushAt 2619 2 1721,
   opAt 2620 .JUMP]

def fallback : List Located :=
  [opAt 2621 .JUMPDEST,
   opAt 2622 (.Dup ⟨0, by decide⟩),
   pushAt 2623 2 4096,
   pushAt 2624 2 1024,
   opAt 2625 .MCOPY,
   pushAt 2626 0 0,
   pushAt 2627 2 1622,
   opAt 2628 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3324 = true :=
  Artifact.isValidJumpDest_index 2556 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3371 = true :=
  Artifact.isValidJumpDest_index 2585 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3391 = true :=
  Artifact.isValidJumpDest_index 2596 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3392 = true :=
  Artifact.isValidJumpDest_index 2597 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3409 = true :=
  Artifact.isValidJumpDest_index 2604 (by rfl)

theorem jumpDest3954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3436 = true :=
  Artifact.isValidJumpDest_index 2618 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3441 = true :=
  Artifact.isValidJumpDest_index 2621 (by rfl)

/-- Actual bypass target around the protected word-path island. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3335 = true :=
  Artifact.isValidJumpDest_index 2563 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
