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

@[simp] theorem directPC0 (i : Nat) (hi : 2430 ≤ i) (hii : i ≤ 2466) :
    Artifact.submissionArtifact.instructionPC i =
      ([3138,3139,3140,3141,3142,3143,3147,3148,3151,3152,3153,3155,3156,3159,3160,3163,3164,3165,3166,3167,3169,3170,3173,3174,3176,3179,3180,3181,3184,3185,3186,3188,3189,3193,3194,3197,3198] : List Nat)[i - 2430]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2467 ≤ i) (hii : i ≤ 2500) :
    Artifact.submissionArtifact.instructionPC i =
      ([3200,3201,3202,3205,3206,3209,3212,3213,3214,3217,3220,3221,3222,3224,3225,3226,3227,3230,3231,3232,3233,3236,3239,3240,3243,3246,3247,3248,3249,3252,3255,3256,3257,3260] : List Nat)[i - 2467]! := by
  interval_cases i <;> decide


-- Fall-through on tip 048082eb: PUSH2 3144; POP -> three JUMPDESTs; PUSH1 3 -> PUSH3 3.
def entryPrefix : List Located :=
  [opAt 2430 .JUMPDEST,
   opAt 2431 (.Dup ⟨3, by decide⟩),
   opAt 2432 .JUMPDEST,
   opAt 2433 .JUMPDEST,
   opAt 2434 .JUMPDEST,
   pushAt 2435 3 3,
   opAt 2436 .EQ,
   pushAt 2437 2 3180,
   opAt 2438 .JUMPI]

def oneWidth : List Located :=
  [opAt 2439 (.Dup ⟨3, by decide⟩),
   pushAt 2440 1 1,
   opAt 2441 .XOR,
   pushAt 2442 2 3247,
   opAt 2443 .JUMPI]

def checkThree : List Located :=
  [pushAt 2444 2 9472,
   opAt 2445 .MLOAD,
   opAt 2446 .CALLDATALOAD,
   pushAt 2447 0 0,
   opAt 2448 .BYTE,
   pushAt 2449 1 3,
   opAt 2450 .XOR,
   pushAt 2451 2 3247,
   opAt 2452 .JUMPI]

def threeHit : List Located :=
  [pushAt 2453 1 1,
   pushAt 2454 2 3200,
   opAt 2455 .JUMP]

def check65537 : List Located :=
  [opAt 2456 .JUMPDEST,
   pushAt 2457 2 9472,
   opAt 2458 .MLOAD,
   opAt 2459 .CALLDATALOAD,
   pushAt 2460 1 232,
   opAt 2461 .SHR,
   pushAt 2462 3 65537,
   opAt 2463 .XOR,
   pushAt 2464 2 3247,
   opAt 2465 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2466 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3233. -/
def squareCall : List Located :=
  [opAt 2467 .JUMPDEST,
   opAt 2468 (.Dup ⟨0, by decide⟩),
   pushAt 2469 2 9280,
   opAt 2470 .MSTORE,
   pushAt 2471 2 3221,
   pushAt 2472 2 2048,
   opAt 2473 (.Dup ⟨0, by decide⟩),
   opAt 2474 (.Dup ⟨0, by decide⟩),
   pushAt 2475 2 4788,
   pushAt 2476 2 3916,
   opAt 2477 .JUMP]

def squareReturn : List Located :=
  [opAt 2478 .JUMPDEST,
   pushAt 2479 1 1,
   opAt 2480 (.Swap ⟨0, by decide⟩),
   opAt 2481 .SUB,
   opAt 2482 (.Dup ⟨0, by decide⟩),
   pushAt 2483 2 3200,
   opAt 2484 .JUMPI]

/-- `after_sq` (pc 3243): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2485 .JUMPDEST,
   opAt 2486 .POP,
   pushAt 2487 2 1571,
   pushAt 2488 2 1024,
   opAt 2489 (.Dup ⟨0, by decide⟩),
   pushAt 2490 2 2048,
   pushAt 2491 2 3912,
   opAt 2492 .JUMP]

def fallback : List Located :=
  [opAt 2493 .JUMPDEST,
   opAt 2494 (.Dup ⟨0, by decide⟩),
   pushAt 2495 2 4096,
   pushAt 2496 2 1024,
   opAt 2497 .MCOPY,
   pushAt 2498 0 0,
   pushAt 2499 2 1474,
   opAt 2500 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3138 = true :=
  Artifact.isValidJumpDest_index 2430 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3180 = true :=
  Artifact.isValidJumpDest_index 2456 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3200 = true :=
  Artifact.isValidJumpDest_index 2467 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3221 = true :=
  Artifact.isValidJumpDest_index 2478 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3247 = true :=
  Artifact.isValidJumpDest_index 2493 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3912 = true :=
  Artifact.isValidJumpDest_index 2953 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3916 = true :=
  Artifact.isValidJumpDest_index 2955 (by rfl)

/-- Target of the (now contiguous) jump from `0x0c6d` to `0x0c71`. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3142 = true :=
  Artifact.isValidJumpDest_index 2434 (by rfl)

/-- `after_sq` (pc 3243): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3231 = true :=
  Artifact.isValidJumpDest_index 2485 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
