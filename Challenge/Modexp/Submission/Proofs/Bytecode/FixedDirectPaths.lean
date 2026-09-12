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

@[simp] theorem directPC0 (i : Nat) (hi : 2505 ≤ i) (hii : i ≤ 2541) :
    Artifact.submissionArtifact.instructionPC i =
      ([3273,3274,3275,3278,3279,3280,3282,3283,3286,3287,3288,3290,3291,3294,3295,3298,3299,3300,3301,3302,3304,3305,3308,3309,3311,3314,3315,3316,3319,3320,3321,3323,3324,3328,3329,3332,3333] : List Nat)[i - 2505]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2542 ≤ i) (hii : i ≤ 2575) :
    Artifact.submissionArtifact.instructionPC i =
      ([3335,3336,3337,3340,3341,3344,3347,3348,3349,3352,3355,3356,3357,3359,3360,3361,3362,3365,3366,3367,3368,3371,3374,3375,3378,3381,3382,3383,3384,3387,3390,3391,3392,3395] : List Nat)[i - 2542]! := by
  interval_cases i <;> decide


-- At index 2433 the pushed target 3144 IS the fall-through pc, and the `JUMPDEST` at
-- 3144 is the next element of this very list, so `POP` lands where `JUMP` did with an
-- identical stack and pc.  Keep this note OUTSIDE the list: a comment between entries is
-- legal Lean, but a line-oriented reader of this list sees the entry as missing.
def entryPrefix : List Located :=
  [opAt 2505 .JUMPDEST,
   opAt 2506 (.Dup ⟨3, by decide⟩),
   pushAt 2507 2 3144,
   opAt 2508 .POP,
   opAt 2509 .JUMPDEST,
   pushAt 2510 1 3,
   opAt 2511 .EQ,
   pushAt 2512 2 3315,
   opAt 2513 .JUMPI]

def oneWidth : List Located :=
  [opAt 2514 (.Dup ⟨3, by decide⟩),
   pushAt 2515 1 1,
   opAt 2516 .XOR,
   pushAt 2517 2 3382,
   opAt 2518 .JUMPI]

def checkThree : List Located :=
  [pushAt 2519 2 9472,
   opAt 2520 .MLOAD,
   opAt 2521 .CALLDATALOAD,
   pushAt 2522 0 0,
   opAt 2523 .BYTE,
   pushAt 2524 1 3,
   opAt 2525 .XOR,
   pushAt 2526 2 3382,
   opAt 2527 .JUMPI]

def threeHit : List Located :=
  [pushAt 2528 1 1,
   pushAt 2529 2 3335,
   opAt 2530 .JUMP]

def check65537 : List Located :=
  [opAt 2531 .JUMPDEST,
   pushAt 2532 2 9472,
   opAt 2533 .MLOAD,
   opAt 2534 .CALLDATALOAD,
   pushAt 2535 1 232,
   opAt 2536 .SHR,
   pushAt 2537 3 65537,
   opAt 2538 .XOR,
   pushAt 2539 2 3382,
   opAt 2540 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2541 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3233. -/
def squareCall : List Located :=
  [opAt 2542 .JUMPDEST,
   opAt 2543 (.Dup ⟨0, by decide⟩),
   pushAt 2544 2 9280,
   opAt 2545 .MSTORE,
   pushAt 2546 2 3356,
   pushAt 2547 2 2048,
   opAt 2548 (.Dup ⟨0, by decide⟩),
   opAt 2549 (.Dup ⟨0, by decide⟩),
   pushAt 2550 2 4923,
   pushAt 2551 2 4051,
   opAt 2552 .JUMP]

def squareReturn : List Located :=
  [opAt 2553 .JUMPDEST,
   pushAt 2554 1 1,
   opAt 2555 (.Swap ⟨0, by decide⟩),
   opAt 2556 .SUB,
   opAt 2557 (.Dup ⟨0, by decide⟩),
   pushAt 2558 2 3335,
   opAt 2559 .JUMPI]

/-- `after_sq` (pc 3243): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2560 .JUMPDEST,
   opAt 2561 .POP,
   pushAt 2562 2 1706,
   pushAt 2563 2 1024,
   opAt 2564 (.Dup ⟨0, by decide⟩),
   pushAt 2565 2 2048,
   pushAt 2566 2 4047,
   opAt 2567 .JUMP]

def fallback : List Located :=
  [opAt 2568 .JUMPDEST,
   opAt 2569 (.Dup ⟨0, by decide⟩),
   pushAt 2570 2 4096,
   pushAt 2571 2 1024,
   opAt 2572 .MCOPY,
   pushAt 2573 0 0,
   pushAt 2574 2 1609,
   opAt 2575 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3273 = true :=
  Artifact.isValidJumpDest_index 2505 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3315 = true :=
  Artifact.isValidJumpDest_index 2531 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3335 = true :=
  Artifact.isValidJumpDest_index 2542 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3356 = true :=
  Artifact.isValidJumpDest_index 2553 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3382 = true :=
  Artifact.isValidJumpDest_index 2568 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4047 = true :=
  Artifact.isValidJumpDest_index 3028 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4051 = true :=
  Artifact.isValidJumpDest_index 3030 (by rfl)

/-- Target of the (now contiguous) jump from `0x0c6d` to `0x0c71`. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3279 = true :=
  Artifact.isValidJumpDest_index 2509 (by rfl)

/-- `after_sq` (pc 3243): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3366 = true :=
  Artifact.isValidJumpDest_index 2560 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
