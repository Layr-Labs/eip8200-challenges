import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The appended handler occupies pc3892..3523 and instruction indices2572..2308.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat)
    (hi : 2434 ≤ i) (hii : i ≤ 2470) :
    Artifact.submissionArtifact.instructionPC i =
      ([3395,3396,3397,3399,3400,3403,3404,3405,3407,3408,3409,3412,3413,3416,3417,3418,3419,3420,3422,3423,3424,3427,3428,3430,3433,3434,3435,3438,3439,3440,3442,3443,3447,3448,3449,3452,3453] : List Nat)[i - 2434]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2471 ≤ i) (hii : i ≤ 2503) :
    Artifact.submissionArtifact.instructionPC i =
      ([3455,3456,3457,3460,3463,3466,3469,3472,3473,3474,3476,3477,3478,3479,3482,3483,3484,3487,3490,3493,3496,3499,3500,3501,3504,3505,3506,3507,3510,3513,3514,3515,3518] : List Nat)[i - 2471]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2434 .JUMPDEST, opAt 2435 (.Dup ⟨3, by decide⟩),
   pushAt 2436 1 3, opAt 2437 .EQ, pushAt 2438 2 3434,
   opAt 2439 .JUMPI]

def oneWidth : List Located :=
  [opAt 2440 (.Dup ⟨3, by decide⟩), pushAt 2441 1 1,
   opAt 2442 .EQ, opAt 2443 .ISZERO, pushAt 2444 2 3505,
   opAt 2445 .JUMPI]

def checkThree : List Located :=
  [pushAt 2446 2 9472, opAt 2447 .MLOAD, opAt 2448 .CALLDATALOAD,
   pushAt 2449 0 0, opAt 2450 .BYTE, pushAt 2451 1 3,
   opAt 2452 .EQ, opAt 2453 .ISZERO, pushAt 2454 2 3505,
   opAt 2455 .JUMPI]

def threeHit : List Located :=
  [pushAt 2456 1 1, pushAt 2457 2 3455, opAt 2458 .JUMP]

def check65537 : List Located :=
  [opAt 2459 .JUMPDEST, pushAt 2460 2 9472, opAt 2461 .MLOAD,
   opAt 2462 .CALLDATALOAD, pushAt 2463 1 232, opAt 2464 .SHR,
   pushAt 2465 3 65537, opAt 2466 .EQ, opAt 2467 .ISZERO,
   pushAt 2468 2 3505, opAt 2469 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2470 1 16]

def start : List Located :=
  [opAt 2471 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2472 .JUMPDEST, pushAt 2473 2 3473, pushAt 2474 2 2048,
   pushAt 2475 2 2048, pushAt 2476 2 2048, pushAt 2477 2 4202,
   opAt 2478 .JUMP]

def squareReturn : List Located :=
  [opAt 2479 .JUMPDEST, pushAt 2480 1 1,
   opAt 2481 (.Swap ⟨0, by decide⟩), opAt 2482 .SUB,
   opAt 2483 (.Dup ⟨0, by decide⟩), pushAt 2484 2 3456,
   opAt 2485 .JUMPI]

def product : List Located :=
  [opAt 2486 .POP, pushAt 2487 2 3500, pushAt 2488 2 1024,
   pushAt 2489 2 1024, pushAt 2490 2 2048, pushAt 2491 2 4202,
   opAt 2492 .JUMP]

def finish : List Located :=
  [opAt 2493 .JUMPDEST, pushAt 2494 2 1876, opAt 2495 .JUMP]

def fallback : List Located :=
  [opAt 2496 .JUMPDEST, opAt 2497 (.Dup ⟨0, by decide⟩),
   pushAt 2498 2 4096, pushAt 2499 2 1024, opAt 2500 .MCOPY,
   pushAt 2501 0 0, pushAt 2502 2 1769, opAt 2503 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3395 = true :=
  Artifact.isValidJumpDest_index 2434 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3434 = true :=
  Artifact.isValidJumpDest_index 2459 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3455 = true :=
  Artifact.isValidJumpDest_index 2471 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3456 = true :=
  Artifact.isValidJumpDest_index 2472 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3473 = true :=
  Artifact.isValidJumpDest_index 2479 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3500 = true :=
  Artifact.isValidJumpDest_index 2493 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3505 = true :=
  Artifact.isValidJumpDest_index 2496 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
