import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 160000
set_option maxHeartbeats 16000000

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
      ([3138,3139,3140,3143,3144,3145,3147,3148,3151,3152,3153,3155,3156,3159,3160,3163,3164,3165,3166,3167,3169,3170,3173,3174,3176,3179,3180,3181,3184,3185,3186,3188,3189,3193,3194,3197,3198] : List Nat)[i - 2430]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2467 ≤ i) (hii : i ≤ 2500) :
    Artifact.submissionArtifact.instructionPC i =
      ([3200,3201,3202,3205,3206,3209,3212,3213,3214,3217,3220,3221,3222,3224,3225,3226,3227,3230,3231,3232,3233,3236,3239,3240,3243,3246,3247,3248,3249,3252,3255,3256,3257,3260] : List Nat)[i - 2467]! := by
  interval_cases i <;> decide


-- At index 2433 the pushed target 3144 IS the fall-through pc, and the `JUMPDEST` at
-- 3144 is the next element of this very list, so `POP` lands where `JUMP` did with an
-- identical stack and pc.  Keep this note OUTSIDE the list: a comment between entries is
-- legal Lean, but a line-oriented reader of this list sees the entry as missing.
def entryPrefix : List Located :=
  [opAt 2426 .JUMPDEST,
   opAt 2427 (.Dup ⟨3, by decide⟩),
   opAt 2428 .JUMPDEST,
   pushAt 2429 1 3,
   opAt 2430 .EQ,
   pushAt 2431 2 3168,
   opAt 2432 .JUMPI]

def oneWidth : List Located :=
  [opAt 2433 (.Dup ⟨3, by decide⟩),
   pushAt 2434 1 1,
   opAt 2435 .XOR,
   pushAt 2436 2 3235,
   opAt 2437 .JUMPI]

def checkThree : List Located :=
  [pushAt 2438 2 9472,
   opAt 2439 .MLOAD,
   opAt 2440 .CALLDATALOAD,
   pushAt 2441 0 0,
   opAt 2442 .BYTE,
   pushAt 2443 1 3,
   opAt 2444 .XOR,
   pushAt 2445 2 3235,
   opAt 2446 .JUMPI]

def threeHit : List Located :=
  [pushAt 2447 1 1,
   pushAt 2448 2 3188,
   opAt 2449 .JUMP]

def check65537 : List Located :=
  [opAt 2450 .JUMPDEST,
   pushAt 2451 2 9472,
   opAt 2452 .MLOAD,
   opAt 2453 .CALLDATALOAD,
   pushAt 2454 1 232,
   opAt 2455 .SHR,
   pushAt 2456 3 65537,
   opAt 2457 .XOR,
   pushAt 2458 2 3235,
   opAt 2459 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2460 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3233. -/
def squareCall : List Located :=
  [opAt 2461 .JUMPDEST,
   opAt 2462 (.Dup ⟨0, by decide⟩),
   pushAt 2463 2 9280,
   opAt 2464 .MSTORE,
   pushAt 2465 2 3209,
   pushAt 2466 2 2048,
   opAt 2467 (.Dup ⟨0, by decide⟩),
   opAt 2468 (.Dup ⟨0, by decide⟩),
   pushAt 2469 2 4772,
   pushAt 2470 2 3904,
   opAt 2471 .JUMP]

def squareReturn : List Located :=
  [opAt 2472 .JUMPDEST,
   pushAt 2473 1 1,
   opAt 2474 (.Swap ⟨0, by decide⟩),
   opAt 2475 .SUB,
   opAt 2476 (.Dup ⟨0, by decide⟩),
   pushAt 2477 2 3188,
   opAt 2478 .JUMPI]

/-- `after_sq` (pc 3243): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2479 .JUMPDEST,
   opAt 2480 .POP,
   pushAt 2481 2 1567,
   pushAt 2482 2 1024,
   opAt 2483 (.Dup ⟨0, by decide⟩),
   pushAt 2484 2 2048,
   pushAt 2485 2 3900,
   opAt 2486 .JUMP]

def fallback : List Located :=
  [opAt 2487 .JUMPDEST,
   opAt 2488 (.Dup ⟨0, by decide⟩),
   pushAt 2489 2 4096,
   pushAt 2490 2 1024,
   opAt 2491 .MCOPY,
   pushAt 2492 0 0,
   pushAt 2493 2 1470,
   opAt 2494 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3130 = true :=
  Artifact.isValidJumpDest_index 2426 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3168 = true :=
  Artifact.isValidJumpDest_index 2450 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3188 = true :=
  Artifact.isValidJumpDest_index 2461 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3209 = true :=
  Artifact.isValidJumpDest_index 2472 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3235 = true :=
  Artifact.isValidJumpDest_index 2487 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3900 = true :=
  Artifact.isValidJumpDest_index 2947 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3904 = true :=
  Artifact.isValidJumpDest_index 2949 (by rfl)

/-- Target of the (now contiguous) jump from `0x0c6d` to `0x0c71`. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3132 = true :=
  Artifact.isValidJumpDest_index 2428 (by rfl)

/-- `after_sq` (pc 3243): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3219 = true :=
  Artifact.isValidJumpDest_index 2479 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
