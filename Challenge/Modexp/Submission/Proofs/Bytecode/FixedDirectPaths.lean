import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3289 (`0x0c6b`).  Each in-place square enters
the kernel's shared `common` block with `hd = sq_row`; the final
mixed-domain product enters the kernel's multiply entry.  For the accelerated
widths the kernel loops internally and returns to `after_sq` (pc 3352), so the
loop head first stores the square count in memory word `0x2440 = 9280`.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2481 ≤ i) (hii : i ≤ 2514) :
    Artifact.submissionArtifact.instructionPC i =
      ([3265,3266,3267,3269,3270,3273,3274,3275,3277,3278,3281,3282,3285,3286,3287,3288,3289,3291,3292,3295,3296,3298,3301,3302,3303,3306,3307,3308,3310,3311,3315,3316,3319,3320] : List Nat)[i - 2481]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2515 ≤ i) (hii : i ≤ 2548) :
    Artifact.submissionArtifact.instructionPC i =
      ([3322,3323,3324,3327,3328,3331,3334,3335,3336,3339,3342,3343,3344,3345,3346,3347,3348,3351,3352,3353,3354,3357,3360,3361,3364,3367,3368,3369,3370,3373,3376,3377,3378,3381] : List Nat)[i - 2515]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2481 .JUMPDEST,
   opAt 2482 (.Dup ⟨3, by decide⟩),
   pushAt 2483 1 3,
   opAt 2484 .EQ,
   pushAt 2485 2 3302,
   opAt 2486 .JUMPI]

def oneWidth : List Located :=
  [opAt 2487 (.Dup ⟨3, by decide⟩),
   pushAt 2488 1 1,
   opAt 2489 .XOR,
   pushAt 2490 2 3368,
   opAt 2491 .JUMPI]

def checkThree : List Located :=
  [pushAt 2492 2 2816,
   opAt 2493 .MLOAD,
   opAt 2494 .CALLDATALOAD,
   pushAt 2495 0 0,
   opAt 2496 .BYTE,
   pushAt 2497 1 3,
   opAt 2498 .XOR,
   pushAt 2499 2 3368,
   opAt 2500 .JUMPI]

def threeHit : List Located :=
  [pushAt 2501 1 1,
   pushAt 2502 2 3322,
   opAt 2503 .JUMP]

def check65537 : List Located :=
  [opAt 2504 .JUMPDEST,
   pushAt 2505 2 2816,
   opAt 2506 .MLOAD,
   opAt 2507 .CALLDATALOAD,
   pushAt 2508 1 232,
   opAt 2509 .SHR,
   pushAt 2510 3 65537,
   opAt 2511 .XOR,
   pushAt 2512 2 3368,
   opAt 2513 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2514 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3343. -/
def squareCall : List Located :=
  [opAt 2515 .JUMPDEST,
   opAt 2516 (.Dup ⟨0, by decide⟩),
   pushAt 2517 2 2624,
   opAt 2518 .MSTORE,
   pushAt 2519 2 3343,
   pushAt 2520 2 512,
   opAt 2521 (.Dup ⟨0, by decide⟩),
   opAt 2522 (.Dup ⟨0, by decide⟩),
   pushAt 2523 2 5294,
   pushAt 2524 2 4145,
   opAt 2525 .JUMP]

def squareReturn : List Located :=
  [opAt 2526 .JUMPDEST,
   pushAt 2527 0 0,
   opAt 2528 .NOT,
   opAt 2529 .ADD,
   opAt 2530 (.Dup ⟨0, by decide⟩),
   pushAt 2531 2 3322,
   opAt 2532 .JUMPI]

/-- `after_sq` (pc 3352): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2533 .JUMPDEST,
   opAt 2534 .POP,
   pushAt 2535 2 1696,
   pushAt 2536 2 256,
   opAt 2537 (.Dup ⟨0, by decide⟩),
   pushAt 2538 2 512,
   pushAt 2539 2 4141,
   opAt 2540 .JUMP]

def fallback : List Located :=
  [opAt 2541 .JUMPDEST,
   opAt 2542 (.Dup ⟨0, by decide⟩),
   pushAt 2543 2 1024,
   pushAt 2544 2 256,
   opAt 2545 .MCOPY,
   pushAt 2546 0 0,
   pushAt 2547 2 1599,
   opAt 2548 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3265 = true :=
  Artifact.isValidJumpDest_index 2481 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3302 = true :=
  Artifact.isValidJumpDest_index 2504 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3322 = true :=
  Artifact.isValidJumpDest_index 2515 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3343 = true :=
  Artifact.isValidJumpDest_index 2526 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3368 = true :=
  Artifact.isValidJumpDest_index 2541 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4141 = true :=
  Artifact.isValidJumpDest_index 3134 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4145 = true :=
  Artifact.isValidJumpDest_index 3136 (by rfl)


/-- `after_sq` (pc 3352): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3352 = true :=
  Artifact.isValidJumpDest_index 2533 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
