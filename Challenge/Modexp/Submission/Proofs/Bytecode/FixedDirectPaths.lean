import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3171 (`0x0c6b`).  Each in-place square enters
the kernel's shared `common` block with `hd = sq_row`; the final
mixed-domain product enters the kernel's multiply entry.  For the accelerated
widths the kernel loops internally and returns to `after_sq` (pc 3234), so the
loop head first stores the square count in memory word `0x2440 = 9280`.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2433 ≤ i) (hii : i ≤ 2467) :
    Artifact.submissionArtifact.instructionPC i =
      ([3146,3147,3148,3149,3151,3152,3155,3156,3157,3159,3160,3163,3164,3167,3168,3169,3170,3171,3173,3174,3177,3178,3180,3183,3184,3185,3188,3189,3190,3192,3193,3197,3198,3201,3202] : List Nat)[i - 2433]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2468 ≤ i) (hii : i ≤ 2501) :
    Artifact.submissionArtifact.instructionPC i =
      ([3204,3205,3206,3209,3210,3213,3216,3217,3218,3221,3224,3225,3226,3227,3228,3229,3230,3233,3234,3235,3236,3239,3242,3243,3246,3249,3250,3251,3252,3255,3258,3259,3260,3263] : List Nat)[i - 2468]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2433 .JUMPDEST,
   opAt 2434 (.Dup ⟨3, by decide⟩),
   opAt 2435 .JUMPDEST,
   pushAt 2436 1 3,
   opAt 2437 .EQ,
   pushAt 2438 2 3184,
   opAt 2439 .JUMPI]

def oneWidth : List Located :=
  [opAt 2440 (.Dup ⟨3, by decide⟩),
   pushAt 2441 1 1,
   opAt 2442 .XOR,
   pushAt 2443 2 3250,
   opAt 2444 .JUMPI]

def checkThree : List Located :=
  [pushAt 2445 2 9472,
   opAt 2446 .MLOAD,
   opAt 2447 .CALLDATALOAD,
   pushAt 2448 0 0,
   opAt 2449 .BYTE,
   pushAt 2450 1 3,
   opAt 2451 .XOR,
   pushAt 2452 2 3250,
   opAt 2453 .JUMPI]

def threeHit : List Located :=
  [pushAt 2454 1 1,
   pushAt 2455 2 3204,
   opAt 2456 .JUMP]

def check65537 : List Located :=
  [opAt 2457 .JUMPDEST,
   pushAt 2458 2 9472,
   opAt 2459 .MLOAD,
   opAt 2460 .CALLDATALOAD,
   pushAt 2461 1 232,
   opAt 2462 .SHR,
   pushAt 2463 3 65537,
   opAt 2464 .XOR,
   pushAt 2465 2 3250,
   opAt 2466 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2467 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3225. -/
def squareCall : List Located :=
  [opAt 2468 .JUMPDEST,
   opAt 2469 (.Dup ⟨0, by decide⟩),
   pushAt 2470 2 9280,
   opAt 2471 .MSTORE,
   pushAt 2472 2 3225,
   pushAt 2473 2 2048,
   opAt 2474 (.Dup ⟨0, by decide⟩),
   opAt 2475 (.Dup ⟨0, by decide⟩),
   pushAt 2476 2 4724,
   pushAt 2477 2 3866,
   opAt 2478 .JUMP]

def squareReturn : List Located :=
  [opAt 2479 .JUMPDEST,
   pushAt 2480 0 0,
   opAt 2481 .NOT,
   opAt 2482 .ADD,
   opAt 2483 (.Dup ⟨0, by decide⟩),
   pushAt 2484 2 3204,
   opAt 2485 .JUMPI]

/-- `after_sq` (pc 3234): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2486 .JUMPDEST,
   opAt 2487 .POP,
   pushAt 2488 2 1583,
   pushAt 2489 2 1024,
   opAt 2490 (.Dup ⟨0, by decide⟩),
   pushAt 2491 2 2048,
   pushAt 2492 2 3862,
   opAt 2493 .JUMP]

def fallback : List Located :=
  [opAt 2494 .JUMPDEST,
   opAt 2495 (.Dup ⟨0, by decide⟩),
   pushAt 2496 2 4096,
   pushAt 2497 2 1024,
   opAt 2498 .MCOPY,
   pushAt 2499 0 0,
   pushAt 2500 2 1486,
   opAt 2501 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3146 = true :=
  Artifact.isValidJumpDest_index 2433 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3184 = true :=
  Artifact.isValidJumpDest_index 2457 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3204 = true :=
  Artifact.isValidJumpDest_index 2468 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3225 = true :=
  Artifact.isValidJumpDest_index 2479 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3250 = true :=
  Artifact.isValidJumpDest_index 2494 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3862 = true :=
  Artifact.isValidJumpDest_index 2946 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3866 = true :=
  Artifact.isValidJumpDest_index 2948 (by rfl)

/-- Target of the (now contiguous) jump from `0x0c6d` to `0x0c71`. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3148 = true :=
  Artifact.isValidJumpDest_index 2435 (by rfl)

/-- `after_sq` (pc 3234): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3234 = true :=
  Artifact.isValidJumpDest_index 2486 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
