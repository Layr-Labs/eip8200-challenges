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

@[simp] theorem directPC0 (i : Nat) (hi : 2552 ≤ i) (hii : i ≤ 2591) :
    Artifact.submissionArtifact.instructionPC i =
      ([3324,3325,3326,3329,3330,3331,3334,3335,3336,3338,3339,3342,3343,3344,3346,3347,3350,3351,3354,3355,3356,3357,3358,3360,3361,3364,3365,3367,3370,3371,3372,3375,3376,3377,3379,3380,3384,3385,3388,3389] : List Nat)[i - 2552]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2592 ≤ i) (hii : i ≤ 2624) :
    Artifact.submissionArtifact.instructionPC i =
      ([3391,3392,3393,3396,3399,3402,3405,3408,3409,3410,3412,3413,3414,3415,3418,3419,3420,3423,3426,3429,3432,3435,3436,3437,3440,3441,3442,3443,3446,3449,3450,3451,3454] : List Nat)[i - 2592]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2552 .JUMPDEST,
   opAt 2553 (.Dup ⟨3, by decide⟩),
   pushAt 2554 2 3335,
   opAt 2555 .JUMP,
   opAt 2559 .JUMPDEST,
   pushAt 2560 1 3,
   opAt 2561 .EQ,
   pushAt 2562 2 3371,
   opAt 2563 .JUMPI]

def oneWidth : List Located :=
  [opAt 2564 (.Dup ⟨3, by decide⟩),
   pushAt 2565 1 1,
   opAt 2566 .XOR,
   pushAt 2567 2 3441,
   opAt 2568 .JUMPI]

def checkThree : List Located :=
  [pushAt 2569 2 9472,
   opAt 2570 .MLOAD,
   opAt 2571 .CALLDATALOAD,
   pushAt 2572 0 0,
   opAt 2573 .BYTE,
   pushAt 2574 1 3,
   opAt 2575 .XOR,
   pushAt 2576 2 3441,
   opAt 2577 .JUMPI]

def threeHit : List Located :=
  [pushAt 2578 1 1,
   pushAt 2579 2 3392,
   opAt 2580 .JUMP]

def check65537 : List Located :=
  [opAt 2581 .JUMPDEST,
   pushAt 2582 2 9472,
   opAt 2583 .MLOAD,
   opAt 2584 .CALLDATALOAD,
   pushAt 2585 1 232,
   opAt 2586 .SHR,
   pushAt 2587 3 65537,
   opAt 2588 .XOR,
   pushAt 2589 2 3441,
   opAt 2590 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2591 1 16, opAt 2592 .JUMPDEST]

def start : List Located :=
  []

def squareCall : List Located :=
  [opAt 2593 .JUMPDEST,
   pushAt 2594 2 3409,
   pushAt 2595 2 2048,
   pushAt 2596 2 2048,
   pushAt 2597 2 2048,
   pushAt 2598 2 4053,
   opAt 2599 .JUMP]

def squareReturn : List Located :=
  [opAt 2600 .JUMPDEST,
   pushAt 2601 1 1,
   opAt 2602 (.Swap ⟨0, by decide⟩),
   opAt 2603 .SUB,
   opAt 2604 (.Dup ⟨0, by decide⟩),
   pushAt 2605 2 3392,
   opAt 2606 .JUMPI]

def product : List Located :=
  [opAt 2607 .POP,
   pushAt 2608 2 3436,
   pushAt 2609 2 1024,
   pushAt 2610 2 1024,
   pushAt 2611 2 2048,
   pushAt 2612 2 4053,
   opAt 2613 .JUMP]

def finish : List Located :=
  [opAt 2614 .JUMPDEST,
   pushAt 2615 2 1721,
   opAt 2616 .JUMP]

def fallback : List Located :=
  [opAt 2617 .JUMPDEST,
   opAt 2618 (.Dup ⟨0, by decide⟩),
   pushAt 2619 2 4096,
   pushAt 2620 2 1024,
   opAt 2621 .MCOPY,
   pushAt 2622 0 0,
   pushAt 2623 2 1622,
   opAt 2624 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3324 = true :=
  Artifact.isValidJumpDest_index 2552 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3371 = true :=
  Artifact.isValidJumpDest_index 2581 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3391 = true :=
  Artifact.isValidJumpDest_index 2592 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3392 = true :=
  Artifact.isValidJumpDest_index 2593 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3409 = true :=
  Artifact.isValidJumpDest_index 2600 (by rfl)

theorem jumpDest3954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3436 = true :=
  Artifact.isValidJumpDest_index 2614 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3441 = true :=
  Artifact.isValidJumpDest_index 2617 (by rfl)

/-- Actual bypass target around the protected word-path island. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3335 = true :=
  Artifact.isValidJumpDest_index 2559 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
