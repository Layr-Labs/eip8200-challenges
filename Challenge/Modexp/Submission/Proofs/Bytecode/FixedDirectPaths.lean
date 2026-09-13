import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3240 (`0x0c6b`).  Each in-place square enters
the kernel's shared `common` block with `hd = sq_row`; the final
mixed-domain product enters the kernel's multiply entry.  For the accelerated
widths the kernel loops internally and returns to `after_sq` (pc 3303), so the
loop head first stores the square count in memory word `0x2440 = 9280`.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2437 ≤ i) (hii : i ≤ 2470) :
    Artifact.submissionArtifact.instructionPC i =
      ([3216,3217,3218,3220,3221,3224,3225,3226,3228,3229,3232,3233,3236,3237,3238,3239,3240,3242,3243,3246,3247,3249,3252,3253,3254,3257,3258,3259,3261,3262,3266,3267,3270,3271] : List Nat)[i - 2437]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2471 ≤ i) (hii : i ≤ 2504) :
    Artifact.submissionArtifact.instructionPC i =
      ([3273,3274,3275,3278,3279,3282,3285,3286,3287,3290,3293,3294,3295,3296,3297,3298,3299,3302,3303,3304,3305,3308,3311,3312,3315,3318,3319,3320,3321,3324,3327,3328,3329,3332] : List Nat)[i - 2471]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2437 .JUMPDEST,
   opAt 2438 (.Dup ⟨3, by decide⟩),
   pushAt 2439 1 3,
   opAt 2440 .EQ,
   pushAt 2441 2 3253,
   opAt 2442 .JUMPI]

def oneWidth : List Located :=
  [opAt 2443 (.Dup ⟨3, by decide⟩),
   pushAt 2444 1 1,
   opAt 2445 .XOR,
   pushAt 2446 2 3319,
   opAt 2447 .JUMPI]

def checkThree : List Located :=
  [pushAt 2448 2 2816,
   opAt 2449 .MLOAD,
   opAt 2450 .CALLDATALOAD,
   pushAt 2451 0 0,
   opAt 2452 .BYTE,
   pushAt 2453 1 3,
   opAt 2454 .XOR,
   pushAt 2455 2 3319,
   opAt 2456 .JUMPI]

def threeHit : List Located :=
  [pushAt 2457 1 1,
   pushAt 2458 2 3273,
   opAt 2459 .JUMP]

def check65537 : List Located :=
  [opAt 2460 .JUMPDEST,
   pushAt 2461 2 2816,
   opAt 2462 .MLOAD,
   opAt 2463 .CALLDATALOAD,
   pushAt 2464 1 232,
   opAt 2465 .SHR,
   pushAt 2466 3 65537,
   opAt 2467 .XOR,
   pushAt 2468 2 3319,
   opAt 2469 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2470 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3294. -/
def squareCall : List Located :=
  [opAt 2471 .JUMPDEST,
   opAt 2472 (.Dup ⟨0, by decide⟩),
   pushAt 2473 2 2624,
   opAt 2474 .MSTORE,
   pushAt 2475 2 3294,
   pushAt 2476 2 512,
   opAt 2477 (.Dup ⟨0, by decide⟩),
   opAt 2478 (.Dup ⟨0, by decide⟩),
   pushAt 2479 2 5292,
   pushAt 2480 2 4096,
   opAt 2481 .JUMP]

def squareReturn : List Located :=
  [opAt 2482 .JUMPDEST,
   pushAt 2483 0 0,
   opAt 2484 .NOT,
   opAt 2485 .ADD,
   opAt 2486 (.Dup ⟨0, by decide⟩),
   pushAt 2487 2 3273,
   opAt 2488 .JUMPI]

/-- `after_sq` (pc 3303): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2489 .JUMPDEST,
   opAt 2490 .POP,
   pushAt 2491 2 1698,
   pushAt 2492 2 256,
   opAt 2493 (.Dup ⟨0, by decide⟩),
   pushAt 2494 2 512,
   pushAt 2495 2 4092,
   opAt 2496 .JUMP]

def fallback : List Located :=
  [opAt 2497 .JUMPDEST,
   opAt 2498 (.Dup ⟨0, by decide⟩),
   pushAt 2499 2 1024,
   pushAt 2500 2 256,
   opAt 2501 .MCOPY,
   pushAt 2502 0 0,
   pushAt 2503 2 1599,
   opAt 2504 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3216 = true :=
  Artifact.isValidJumpDest_index 2437 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3253 = true :=
  Artifact.isValidJumpDest_index 2460 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3273 = true :=
  Artifact.isValidJumpDest_index 2471 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3294 = true :=
  Artifact.isValidJumpDest_index 2482 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3319 = true :=
  Artifact.isValidJumpDest_index 2497 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4092 = true :=
  Artifact.isValidJumpDest_index 3090 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4096 = true :=
  Artifact.isValidJumpDest_index 3092 (by rfl)


/-- `after_sq` (pc 3303): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3303 = true :=
  Artifact.isValidJumpDest_index 2489 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
