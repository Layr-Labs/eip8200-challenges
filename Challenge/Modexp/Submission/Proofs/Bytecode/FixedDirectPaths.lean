import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3179 (`0x0c6b`).  Each in-place square enters
the kernel's shared `common` block with `hd = sq_row`; the final
mixed-domain product enters the kernel's multiply entry.  For the accelerated
widths the kernel loops internally and returns to `after_sq` (pc 3243), so the
loop head first stores the square count in memory word `0x2440 = 9280`.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2435 ≤ i) (hii : i ≤ 2471) :
    Artifact.submissionArtifact.instructionPC i =
      ([3150,3151,3152,3155,3156,3157,3159,3160,3163,3164,3165,3167,3168,3171,3172,3175,3176,3177,3178,3179,3181,3182,3185,3186,3188,3191,3192,3193,3196,3197,3198,3200,3201,3205,3206,3209,3210] : List Nat)[i - 2435]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2472 ≤ i) (hii : i ≤ 2505) :
    Artifact.submissionArtifact.instructionPC i =
      ([3212,3213,3214,3217,3218,3221,3224,3225,3226,3229,3232,3233,3234,3236,3237,3238,3239,3242,3243,3244,3245,3248,3251,3252,3255,3258,3259,3260,3261,3264,3267,3268,3269,3272] : List Nat)[i - 2472]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2435 .JUMPDEST,
   opAt 2436 (.Dup ⟨3, by decide⟩),
   pushAt 2437 2 3156,
   opAt 2438 .JUMP,
   opAt 2439 .JUMPDEST,
   pushAt 2440 1 3,
   opAt 2441 .EQ,
   pushAt 2442 2 3192,
   opAt 2443 .JUMPI]

def oneWidth : List Located :=
  [opAt 2444 (.Dup ⟨3, by decide⟩),
   pushAt 2445 1 1,
   opAt 2446 .XOR,
   pushAt 2447 2 3259,
   opAt 2448 .JUMPI]

def checkThree : List Located :=
  [pushAt 2449 2 9472,
   opAt 2450 .MLOAD,
   opAt 2451 .CALLDATALOAD,
   pushAt 2452 0 0,
   opAt 2453 .BYTE,
   pushAt 2454 1 3,
   opAt 2455 .XOR,
   pushAt 2456 2 3259,
   opAt 2457 .JUMPI]

def threeHit : List Located :=
  [pushAt 2458 1 1,
   pushAt 2459 2 3212,
   opAt 2460 .JUMP]

def check65537 : List Located :=
  [opAt 2461 .JUMPDEST,
   pushAt 2462 2 9472,
   opAt 2463 .MLOAD,
   opAt 2464 .CALLDATALOAD,
   pushAt 2465 1 232,
   opAt 2466 .SHR,
   pushAt 2467 3 65537,
   opAt 2468 .XOR,
   pushAt 2469 2 3259,
   opAt 2470 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2471 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3233. -/
def squareCall : List Located :=
  [opAt 2472 .JUMPDEST,
   opAt 2473 (.Dup ⟨0, by decide⟩),
   pushAt 2474 2 9280,
   opAt 2475 .MSTORE,
   pushAt 2476 2 3233,
   pushAt 2477 2 2048,
   opAt 2478 (.Dup ⟨0, by decide⟩),
   opAt 2479 (.Dup ⟨0, by decide⟩),
   pushAt 2480 2 4745,
   pushAt 2481 2 3875,
   opAt 2482 .JUMP]

def squareReturn : List Located :=
  [opAt 2483 .JUMPDEST,
   pushAt 2484 1 1,
   opAt 2485 (.Swap ⟨0, by decide⟩),
   opAt 2486 .SUB,
   opAt 2487 (.Dup ⟨0, by decide⟩),
   pushAt 2488 2 3212,
   opAt 2489 .JUMPI]

/-- `after_sq` (pc 3243): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2490 .JUMPDEST,
   opAt 2491 .POP,
   pushAt 2492 2 1583,
   pushAt 2493 2 1024,
   opAt 2494 (.Dup ⟨0, by decide⟩),
   pushAt 2495 2 2048,
   pushAt 2496 2 3871,
   opAt 2497 .JUMP]

def fallback : List Located :=
  [opAt 2498 .JUMPDEST,
   opAt 2499 (.Dup ⟨0, by decide⟩),
   pushAt 2500 2 4096,
   pushAt 2501 2 1024,
   opAt 2502 .MCOPY,
   pushAt 2503 0 0,
   pushAt 2504 2 1486,
   opAt 2505 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3150 = true :=
  Artifact.isValidJumpDest_index 2435 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3192 = true :=
  Artifact.isValidJumpDest_index 2461 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3212 = true :=
  Artifact.isValidJumpDest_index 2472 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3233 = true :=
  Artifact.isValidJumpDest_index 2483 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3259 = true :=
  Artifact.isValidJumpDest_index 2498 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3871 = true :=
  Artifact.isValidJumpDest_index 2950 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3875 = true :=
  Artifact.isValidJumpDest_index 2952 (by rfl)

/-- Target of the (now contiguous) jump from `0x0c6d` to `0x0c71`. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3156 = true :=
  Artifact.isValidJumpDest_index 2439 (by rfl)

/-- `after_sq` (pc 3243): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3243 = true :=
  Artifact.isValidJumpDest_index 2490 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
