import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3159 (`0x0c6b`).  Each in-place square enters
the kernel's shared `common` block with `hd = sq_row`; the final
mixed-domain product enters the kernel's multiply entry.  For the accelerated
widths the kernel loops internally and returns to `after_sq` (pc 3222), so the
loop head first stores the square count in memory word `0x2440 = 9280`.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2428 ≤ i) (hii : i ≤ 2462) :
    Artifact.submissionArtifact.instructionPC i =
      ([3134,3135,3136,3137,3139,3140,3143,3144,3145,3147,3148,3151,3152,3155,3156,3157,3158,3159,3161,3162,3165,3166,3168,3171,3172,3173,3176,3177,3178,3180,3181,3185,3186,3189,3190] : List Nat)[i - 2428]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2463 ≤ i) (hii : i ≤ 2496) :
    Artifact.submissionArtifact.instructionPC i =
      ([3192,3193,3194,3197,3198,3201,3204,3205,3206,3209,3212,3213,3214,3215,3216,3217,3218,3221,3222,3223,3224,3227,3230,3231,3234,3237,3238,3239,3240,3243,3246,3247,3248,3251] : List Nat)[i - 2463]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2428 .JUMPDEST,
   opAt 2429 (.Dup ⟨3, by decide⟩),
   opAt 2430 .JUMPDEST,
   pushAt 2431 1 3,
   opAt 2432 .EQ,
   pushAt 2433 2 3172,
   opAt 2434 .JUMPI]

def oneWidth : List Located :=
  [opAt 2435 (.Dup ⟨3, by decide⟩),
   pushAt 2436 1 1,
   opAt 2437 .XOR,
   pushAt 2438 2 3238,
   opAt 2439 .JUMPI]

def checkThree : List Located :=
  [pushAt 2440 2 9472,
   opAt 2441 .MLOAD,
   opAt 2442 .CALLDATALOAD,
   pushAt 2443 0 0,
   opAt 2444 .BYTE,
   pushAt 2445 1 3,
   opAt 2446 .XOR,
   pushAt 2447 2 3238,
   opAt 2448 .JUMPI]

def threeHit : List Located :=
  [pushAt 2449 1 1,
   pushAt 2450 2 3192,
   opAt 2451 .JUMP]

def check65537 : List Located :=
  [opAt 2452 .JUMPDEST,
   pushAt 2453 2 9472,
   opAt 2454 .MLOAD,
   opAt 2455 .CALLDATALOAD,
   pushAt 2456 1 232,
   opAt 2457 .SHR,
   pushAt 2458 3 65537,
   opAt 2459 .XOR,
   pushAt 2460 2 3238,
   opAt 2461 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2462 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3213. -/
def squareCall : List Located :=
  [opAt 2463 .JUMPDEST,
   opAt 2464 (.Dup ⟨0, by decide⟩),
   pushAt 2465 2 9280,
   opAt 2466 .MSTORE,
   pushAt 2467 2 3213,
   pushAt 2468 2 2048,
   opAt 2469 (.Dup ⟨0, by decide⟩),
   opAt 2470 (.Dup ⟨0, by decide⟩),
   pushAt 2471 2 4734,
   pushAt 2472 2 3877,
   opAt 2473 .JUMP]

def squareReturn : List Located :=
  [opAt 2474 .JUMPDEST,
   pushAt 2475 0 0,
   opAt 2476 .NOT,
   opAt 2477 .ADD,
   opAt 2478 (.Dup ⟨0, by decide⟩),
   pushAt 2479 2 3192,
   opAt 2480 .JUMPI]

/-- `after_sq` (pc 3222): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2481 .JUMPDEST,
   opAt 2482 .POP,
   pushAt 2483 2 1571,
   pushAt 2484 2 1024,
   opAt 2485 (.Dup ⟨0, by decide⟩),
   pushAt 2486 2 2048,
   pushAt 2487 2 3873,
   opAt 2488 .JUMP]

def fallback : List Located :=
  [opAt 2489 .JUMPDEST,
   opAt 2490 (.Dup ⟨0, by decide⟩),
   pushAt 2491 2 4096,
   pushAt 2492 2 1024,
   opAt 2493 .MCOPY,
   pushAt 2494 0 0,
   pushAt 2495 2 1474,
   opAt 2496 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3134 = true :=
  Artifact.isValidJumpDest_index 2428 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3172 = true :=
  Artifact.isValidJumpDest_index 2452 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3192 = true :=
  Artifact.isValidJumpDest_index 2463 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3213 = true :=
  Artifact.isValidJumpDest_index 2474 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3238 = true :=
  Artifact.isValidJumpDest_index 2489 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3873 = true :=
  Artifact.isValidJumpDest_index 2951 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3877 = true :=
  Artifact.isValidJumpDest_index 2953 (by rfl)

/-- Target of the (now contiguous) jump from `0x0c6d` to `0x0c71`. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3136 = true :=
  Artifact.isValidJumpDest_index 2430 (by rfl)

/-- `after_sq` (pc 3222): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3222 = true :=
  Artifact.isValidJumpDest_index 2481 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
