import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3285 (`0x0c6b`).  Each in-place square enters
the kernel's shared `common` block with `hd = sq_row`; the final
mixed-domain product enters the kernel's multiply entry.  For the accelerated
widths the kernel loops internally and returns to `after_sq` (pc 3348), so the
loop head first stores the square count in memory word `0x2440 = 9280`.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2498 ≤ i) (hii : i ≤ 2531) :
    Artifact.submissionArtifact.instructionPC i =
      ([3261,3262,3263,3265,3266,3269,3270,3271,3273,3274,3277,3278,3281,3282,3283,3284,3285,3287,3288,3291,3292,3294,3297,3298,3299,3302,3303,3304,3306,3307,3311,3312,3315,3316] : List Nat)[i - 2498]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2532 ≤ i) (hii : i ≤ 2565) :
    Artifact.submissionArtifact.instructionPC i =
      ([3318,3319,3320,3323,3324,3327,3330,3331,3332,3335,3338,3339,3340,3341,3342,3343,3344,3347,3348,3349,3350,3353,3356,3357,3360,3363,3364,3365,3366,3369,3372,3373,3374,3377] : List Nat)[i - 2532]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2498 .JUMPDEST,
   opAt 2499 (.Dup ⟨3, by decide⟩),
   pushAt 2500 1 3,
   opAt 2501 .EQ,
   pushAt 2502 2 3298,
   opAt 2503 .JUMPI]

def oneWidth : List Located :=
  [opAt 2504 (.Dup ⟨3, by decide⟩),
   pushAt 2505 1 1,
   opAt 2506 .XOR,
   pushAt 2507 2 3364,
   opAt 2508 .JUMPI]

def checkThree : List Located :=
  [pushAt 2509 2 5376,
   opAt 2510 .MLOAD,
   opAt 2511 .CALLDATALOAD,
   pushAt 2512 0 0,
   opAt 2513 .BYTE,
   pushAt 2514 1 3,
   opAt 2515 .XOR,
   pushAt 2516 2 3364,
   opAt 2517 .JUMPI]

def threeHit : List Located :=
  [pushAt 2518 1 1,
   pushAt 2519 2 3318,
   opAt 2520 .JUMP]

def check65537 : List Located :=
  [opAt 2521 .JUMPDEST,
   pushAt 2522 2 5376,
   opAt 2523 .MLOAD,
   opAt 2524 .CALLDATALOAD,
   pushAt 2525 1 232,
   opAt 2526 .SHR,
   pushAt 2527 3 65537,
   opAt 2528 .XOR,
   pushAt 2529 2 3364,
   opAt 2530 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2531 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3339. -/
def squareCall : List Located :=
  [opAt 2532 .JUMPDEST,
   opAt 2533 (.Dup ⟨0, by decide⟩),
   pushAt 2534 2 5184,
   opAt 2535 .MSTORE,
   pushAt 2536 2 3339,
   pushAt 2537 2 512,
   opAt 2538 (.Dup ⟨0, by decide⟩),
   opAt 2539 (.Dup ⟨0, by decide⟩),
   pushAt 2540 2 4984,
   pushAt 2541 2 4141,
   opAt 2542 .JUMP]

def squareReturn : List Located :=
  [opAt 2543 .JUMPDEST,
   pushAt 2544 0 0,
   opAt 2545 .NOT,
   opAt 2546 .ADD,
   opAt 2547 (.Dup ⟨0, by decide⟩),
   pushAt 2548 2 3318,
   opAt 2549 .JUMPI]

/-- `after_sq` (pc 3348): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2550 .JUMPDEST,
   opAt 2551 .POP,
   pushAt 2552 2 1701,
   pushAt 2553 2 256,
   opAt 2554 (.Dup ⟨0, by decide⟩),
   pushAt 2555 2 512,
   pushAt 2556 2 4137,
   opAt 2557 .JUMP]

def fallback : List Located :=
  [opAt 2558 .JUMPDEST,
   opAt 2559 (.Dup ⟨0, by decide⟩),
   pushAt 2560 2 1024,
   pushAt 2561 2 256,
   opAt 2562 .MCOPY,
   pushAt 2563 0 0,
   pushAt 2564 2 1604,
   opAt 2565 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3261 = true :=
  Artifact.isValidJumpDest_index 2498 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3298 = true :=
  Artifact.isValidJumpDest_index 2521 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3318 = true :=
  Artifact.isValidJumpDest_index 2532 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3339 = true :=
  Artifact.isValidJumpDest_index 2543 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3364 = true :=
  Artifact.isValidJumpDest_index 2558 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4137 = true :=
  Artifact.isValidJumpDest_index 3151 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4141 = true :=
  Artifact.isValidJumpDest_index 3153 (by rfl)


/-- `after_sq` (pc 3348): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3348 = true :=
  Artifact.isValidJumpDest_index 2550 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
