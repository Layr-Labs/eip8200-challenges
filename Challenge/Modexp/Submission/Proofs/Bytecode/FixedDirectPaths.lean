import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3203 (`0x0c6b`).  Each in-place square enters
the kernel's shared `common` block with `hd = sq_row`; the final
mixed-domain product enters the kernel's multiply entry.  For the accelerated
widths the kernel loops internally and returns to `after_sq` (pc 3266), so the
loop head first stores the square count in memory word `0x2440 = 9280`.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2460 ≤ i) (hii : i ≤ 2493) :
    Artifact.submissionArtifact.instructionPC i =
      ([3179,3180,3181,3183,3184,3187,3188,3189,3191,3192,3195,3196,3199,3200,3201,3202,3203,3205,3206,3209,3210,3212,3215,3216,3217,3220,3221,3222,3224,3225,3229,3230,3233,3234] : List Nat)[i - 2460]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2494 ≤ i) (hii : i ≤ 2527) :
    Artifact.submissionArtifact.instructionPC i =
      ([3236,3237,3238,3241,3242,3245,3248,3249,3250,3253,3256,3257,3258,3259,3260,3261,3262,3265,3266,3267,3268,3271,3274,3275,3278,3281,3282,3283,3284,3287,3290,3291,3292,3295] : List Nat)[i - 2494]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2460 .JUMPDEST,
   opAt 2461 (.Dup ⟨3, by decide⟩),
   pushAt 2462 1 3,
   opAt 2463 .EQ,
   pushAt 2464 2 3216,
   opAt 2465 .JUMPI]

def oneWidth : List Located :=
  [opAt 2466 (.Dup ⟨3, by decide⟩),
   pushAt 2467 1 1,
   opAt 2468 .XOR,
   pushAt 2469 2 3282,
   opAt 2470 .JUMPI]

def checkThree : List Located :=
  [pushAt 2471 2 9472,
   opAt 2472 .MLOAD,
   opAt 2473 .CALLDATALOAD,
   pushAt 2474 0 0,
   opAt 2475 .BYTE,
   pushAt 2476 1 3,
   opAt 2477 .XOR,
   pushAt 2478 2 3282,
   opAt 2479 .JUMPI]

def threeHit : List Located :=
  [pushAt 2480 1 1,
   pushAt 2481 2 3236,
   opAt 2482 .JUMP]

def check65537 : List Located :=
  [opAt 2483 .JUMPDEST,
   pushAt 2484 2 9472,
   opAt 2485 .MLOAD,
   opAt 2486 .CALLDATALOAD,
   pushAt 2487 1 232,
   opAt 2488 .SHR,
   pushAt 2489 3 65537,
   opAt 2490 .XOR,
   pushAt 2491 2 3282,
   opAt 2492 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2493 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3257. -/
def squareCall : List Located :=
  [opAt 2494 .JUMPDEST,
   opAt 2495 (.Dup ⟨0, by decide⟩),
   pushAt 2496 2 9280,
   opAt 2497 .MSTORE,
   pushAt 2498 2 3257,
   pushAt 2499 2 2048,
   opAt 2500 (.Dup ⟨0, by decide⟩),
   opAt 2501 (.Dup ⟨0, by decide⟩),
   pushAt 2502 2 4902,
   pushAt 2503 2 4059,
   opAt 2504 .JUMP]

def squareReturn : List Located :=
  [opAt 2505 .JUMPDEST,
   pushAt 2506 0 0,
   opAt 2507 .NOT,
   opAt 2508 .ADD,
   opAt 2509 (.Dup ⟨0, by decide⟩),
   pushAt 2510 2 3236,
   opAt 2511 .JUMPI]

/-- `after_sq` (pc 3266): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2512 .JUMPDEST,
   opAt 2513 .POP,
   pushAt 2514 2 1619,
   pushAt 2515 2 1024,
   opAt 2516 (.Dup ⟨0, by decide⟩),
   pushAt 2517 2 2048,
   pushAt 2518 2 4055,
   opAt 2519 .JUMP]

def fallback : List Located :=
  [opAt 2520 .JUMPDEST,
   opAt 2521 (.Dup ⟨0, by decide⟩),
   pushAt 2522 2 4096,
   pushAt 2523 2 1024,
   opAt 2524 .MCOPY,
   pushAt 2525 0 0,
   pushAt 2526 2 1522,
   opAt 2527 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3179 = true :=
  Artifact.isValidJumpDest_index 2460 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3216 = true :=
  Artifact.isValidJumpDest_index 2483 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3236 = true :=
  Artifact.isValidJumpDest_index 2494 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3257 = true :=
  Artifact.isValidJumpDest_index 2505 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3282 = true :=
  Artifact.isValidJumpDest_index 2520 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4055 = true :=
  Artifact.isValidJumpDest_index 3113 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4059 = true :=
  Artifact.isValidJumpDest_index 3115 (by rfl)


/-- `after_sq` (pc 3266): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3266 = true :=
  Artifact.isValidJumpDest_index 2512 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
