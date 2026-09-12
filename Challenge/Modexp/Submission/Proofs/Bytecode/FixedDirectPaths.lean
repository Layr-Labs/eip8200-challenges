import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3299 (`0x0c6b`).  Each in-place square enters
the kernel's shared `common` block with `hd = sq_row`; the final
mixed-domain product enters the kernel's multiply entry.  For the accelerated
widths the kernel loops internally and returns to `after_sq` (pc 3362), so the
loop head first stores the square count in memory word `0x2440 = 9280`.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2487 ≤ i) (hii : i ≤ 2520) :
    Artifact.submissionArtifact.instructionPC i =
      ([3275,3276,3277,3279,3280,3283,3284,3285,3287,3288,3291,3292,3295,3296,3297,3298,3299,3301,3302,3305,3306,3308,3311,3312,3313,3316,3317,3318,3320,3321,3325,3326,3329,3330] : List Nat)[i - 2487]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2521 ≤ i) (hii : i ≤ 2554) :
    Artifact.submissionArtifact.instructionPC i =
      ([3332,3333,3334,3337,3338,3341,3344,3345,3346,3349,3352,3353,3354,3355,3356,3357,3358,3361,3362,3363,3364,3367,3370,3371,3374,3377,3378,3379,3380,3383,3386,3387,3388,3391] : List Nat)[i - 2521]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2487 .JUMPDEST,
   opAt 2488 (.Dup ⟨3, by decide⟩),
   pushAt 2489 1 3,
   opAt 2490 .EQ,
   pushAt 2491 2 3312,
   opAt 2492 .JUMPI]

def oneWidth : List Located :=
  [opAt 2493 (.Dup ⟨3, by decide⟩),
   pushAt 2494 1 1,
   opAt 2495 .XOR,
   pushAt 2496 2 3378,
   opAt 2497 .JUMPI]

def checkThree : List Located :=
  [pushAt 2498 2 5376,
   opAt 2499 .MLOAD,
   opAt 2500 .CALLDATALOAD,
   pushAt 2501 0 0,
   opAt 2502 .BYTE,
   pushAt 2503 1 3,
   opAt 2504 .XOR,
   pushAt 2505 2 3378,
   opAt 2506 .JUMPI]

def threeHit : List Located :=
  [pushAt 2507 1 1,
   pushAt 2508 2 3332,
   opAt 2509 .JUMP]

def check65537 : List Located :=
  [opAt 2510 .JUMPDEST,
   pushAt 2511 2 5376,
   opAt 2512 .MLOAD,
   opAt 2513 .CALLDATALOAD,
   pushAt 2514 1 232,
   opAt 2515 .SHR,
   pushAt 2516 3 65537,
   opAt 2517 .XOR,
   pushAt 2518 2 3378,
   opAt 2519 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2520 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3353. -/
def squareCall : List Located :=
  [opAt 2521 .JUMPDEST,
   opAt 2522 (.Dup ⟨0, by decide⟩),
   pushAt 2523 2 5184,
   opAt 2524 .MSTORE,
   pushAt 2525 2 3353,
   pushAt 2526 2 512,
   opAt 2527 (.Dup ⟨0, by decide⟩),
   opAt 2528 (.Dup ⟨0, by decide⟩),
   pushAt 2529 2 4995,
   pushAt 2530 2 4155,
   opAt 2531 .JUMP]

def squareReturn : List Located :=
  [opAt 2532 .JUMPDEST,
   pushAt 2533 0 0,
   opAt 2534 .NOT,
   opAt 2535 .ADD,
   opAt 2536 (.Dup ⟨0, by decide⟩),
   pushAt 2537 2 3332,
   opAt 2538 .JUMPI]

/-- `after_sq` (pc 3362): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2539 .JUMPDEST,
   opAt 2540 .POP,
   pushAt 2541 2 1701,
   pushAt 2542 2 256,
   opAt 2543 (.Dup ⟨0, by decide⟩),
   pushAt 2544 2 512,
   pushAt 2545 2 4151,
   opAt 2546 .JUMP]

def fallback : List Located :=
  [opAt 2547 .JUMPDEST,
   opAt 2548 (.Dup ⟨0, by decide⟩),
   pushAt 2549 2 1024,
   pushAt 2550 2 256,
   opAt 2551 .MCOPY,
   pushAt 2552 0 0,
   pushAt 2553 2 1604,
   opAt 2554 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3275 = true :=
  Artifact.isValidJumpDest_index 2487 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3312 = true :=
  Artifact.isValidJumpDest_index 2510 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3332 = true :=
  Artifact.isValidJumpDest_index 2521 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3353 = true :=
  Artifact.isValidJumpDest_index 2532 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3378 = true :=
  Artifact.isValidJumpDest_index 2547 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4151 = true :=
  Artifact.isValidJumpDest_index 3140 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4155 = true :=
  Artifact.isValidJumpDest_index 3142 (by rfl)


/-- `after_sq` (pc 3362): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3362 = true :=
  Artifact.isValidJumpDest_index 2539 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
