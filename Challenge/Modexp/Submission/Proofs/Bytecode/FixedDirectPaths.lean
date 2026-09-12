import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3179 (`0x0c6b`).  Each in-place square enters
the kernel's `common` block at pc 3924 with `hd = sq_row` (pc 4710); the final
mixed-domain product enters the multiply entry at pc 3920.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2454 ≤ i) (hii : i ≤ 2490) :
    Artifact.submissionArtifact.instructionPC i =
      ([3179,3180,3181,3184,3185,3186,3188,3189,3192,3193,3194,3196,3197,3200,3201,3204,3205,3206,3207,3208,3210,3211,3214,3215,3217,3220,3221,3222,3225,3226,3227,3229,3230,3234,3235,3238,3239] : List Nat)[i - 2454]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2491 ≤ i) (hii : i ≤ 2520) :
    Artifact.submissionArtifact.instructionPC i =
      ([3241,3242,3245,3248,3249,3250,3253,3256,3257,3258,3260,3261,3262,3263,3266,3267,3268,3271,3274,3275,3278,3281,3282,3283,3284,3287,3290,3291,3292,3295] : List Nat)[i - 2491]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2454 .JUMPDEST,
   opAt 2455 (.Dup ⟨3, by decide⟩),
   pushAt 2456 2 3185,
   opAt 2457 .POP,
   opAt 2458 .JUMPDEST,
   pushAt 2459 1 3,
   opAt 2460 .EQ,
   pushAt 2461 2 3221,
   opAt 2462 .JUMPI]

def oneWidth : List Located :=
  [opAt 2463 (.Dup ⟨3, by decide⟩),
   pushAt 2464 1 1,
   opAt 2465 .XOR,
   pushAt 2466 2 3282,
   opAt 2467 .JUMPI]

def checkThree : List Located :=
  [pushAt 2468 2 2912,
   opAt 2469 .MLOAD,
   opAt 2470 .CALLDATALOAD,
   pushAt 2471 0 0,
   opAt 2472 .BYTE,
   pushAt 2473 1 3,
   opAt 2474 .XOR,
   pushAt 2475 2 3282,
   opAt 2476 .JUMPI]

def threeHit : List Located :=
  [pushAt 2477 1 1,
   pushAt 2478 2 3241,
   opAt 2479 .JUMP]

def check65537 : List Located :=
  [opAt 2480 .JUMPDEST,
   pushAt 2481 2 2912,
   opAt 2482 .MLOAD,
   opAt 2483 .CALLDATALOAD,
   pushAt 2484 1 232,
   opAt 2485 .SHR,
   pushAt 2486 3 65537,
   opAt 2487 .XOR,
   pushAt 2488 2 3282,
   opAt 2489 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2490 1 16]

def start : List Located :=
  []

/-- Loop head: `SQUARE(0x800) → 0x800`, entering the kernel's `common` block
(pc 3924) with `hd = sq_row` (pc 4710) and return address 3257. -/
def squareCall : List Located :=
  [opAt 2491 .JUMPDEST,
   pushAt 2492 2 3257,
   pushAt 2493 2 512,
   opAt 2494 (.Dup ⟨0, by decide⟩),
   opAt 2495 (.Dup ⟨0, by decide⟩),
   pushAt 2496 2 4710,
   pushAt 2497 2 3924,
   opAt 2498 .JUMP]

def squareReturn : List Located :=
  [opAt 2499 .JUMPDEST,
   pushAt 2500 1 1,
   opAt 2501 (.Swap ⟨0, by decide⟩),
   opAt 2502 .SUB,
   opAt 2503 (.Dup ⟨0, by decide⟩),
   pushAt 2504 2 3241,
   opAt 2505 .JUMPI]

def product : List Located :=
  [opAt 2506 .POP,
   pushAt 2507 2 1604,
   pushAt 2508 2 256,
   opAt 2509 (.Dup ⟨0, by decide⟩),
   pushAt 2510 2 512,
   pushAt 2511 2 3920,
   opAt 2512 .JUMP]

def fallback : List Located :=
  [opAt 2513 .JUMPDEST,
   opAt 2514 (.Dup ⟨0, by decide⟩),
   pushAt 2515 2 1024,
   pushAt 2516 2 256,
   opAt 2517 .MCOPY,
   pushAt 2518 0 0,
   pushAt 2519 2 1507,
   opAt 2520 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3179 = true :=
  Artifact.isValidJumpDest_index 2454 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3221 = true :=
  Artifact.isValidJumpDest_index 2480 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3241 = true :=
  Artifact.isValidJumpDest_index 2491 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3257 = true :=
  Artifact.isValidJumpDest_index 2499 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3282 = true :=
  Artifact.isValidJumpDest_index 2513 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3920 = true :=
  Artifact.isValidJumpDest_index 2961 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3924 = true :=
  Artifact.isValidJumpDest_index 2963 (by rfl)

/-- Target of the (now contiguous) jump from `0x0c6d` to `0x0c71`. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3185 = true :=
  Artifact.isValidJumpDest_index 2458 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
