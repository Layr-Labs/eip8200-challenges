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
    (hi : 2418 ≤ i) (hii : i ≤ 2454) :
    Artifact.submissionArtifact.instructionPC i =
      ([3395,3396,3397,3399,3400,3403,3404,3405,3407,3408,3409,3412,3413,3416,3417,3418,3419,3420,3422,3423,3424,3427,3428,3430,3433,3434,3435,3438,3439,3440,3442,3443,3447,3448,3449,3452,3453] : List Nat)[i - 2418]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2455 ≤ i) (hii : i ≤ 2487) :
    Artifact.submissionArtifact.instructionPC i =
      ([3455,3456,3457,3460,3463,3466,3469,3472,3473,3474,3476,3477,3478,3479,3482,3483,3484,3487,3490,3493,3496,3499,3500,3501,3504,3505,3506,3507,3510,3513,3514,3515,3518] : List Nat)[i - 2455]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2418 .JUMPDEST, opAt 2419 (.Dup ⟨3, by decide⟩),
   pushAt 2420 1 3, opAt 2421 .EQ, pushAt 2422 2 3434,
   opAt 2423 .JUMPI]

def oneWidth : List Located :=
  [opAt 2424 (.Dup ⟨3, by decide⟩), pushAt 2425 1 1,
   opAt 2426 .EQ, opAt 2427 .ISZERO, pushAt 2428 2 3505,
   opAt 2429 .JUMPI]

def checkThree : List Located :=
  [pushAt 2430 2 9472, opAt 2431 .MLOAD, opAt 2432 .CALLDATALOAD,
   pushAt 2433 0 0, opAt 2434 .BYTE, pushAt 2435 1 3,
   opAt 2436 .EQ, opAt 2437 .ISZERO, pushAt 2438 2 3505,
   opAt 2439 .JUMPI]

def threeHit : List Located :=
  [pushAt 2440 1 1, pushAt 2441 2 3455, opAt 2442 .JUMP]

def check65537 : List Located :=
  [opAt 2443 .JUMPDEST, pushAt 2444 2 9472, opAt 2445 .MLOAD,
   opAt 2446 .CALLDATALOAD, pushAt 2447 1 232, opAt 2448 .SHR,
   pushAt 2449 3 65537, opAt 2450 .EQ, opAt 2451 .ISZERO,
   pushAt 2452 2 3505, opAt 2453 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2454 1 16]

def start : List Located :=
  [opAt 2455 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2456 .JUMPDEST, pushAt 2457 2 3473, pushAt 2458 2 2048,
   pushAt 2459 2 2048, pushAt 2460 2 2048, pushAt 2461 2 4202,
   opAt 2462 .JUMP]

def squareReturn : List Located :=
  [opAt 2463 .JUMPDEST, pushAt 2464 1 1,
   opAt 2465 (.Swap ⟨0, by decide⟩), opAt 2466 .SUB,
   opAt 2467 (.Dup ⟨0, by decide⟩), pushAt 2468 2 3456,
   opAt 2469 .JUMPI]

def product : List Located :=
  [opAt 2470 .POP, pushAt 2471 2 3500, pushAt 2472 2 1024,
   pushAt 2473 2 1024, pushAt 2474 2 2048, pushAt 2475 2 4202,
   opAt 2476 .JUMP]

def finish : List Located :=
  [opAt 2477 .JUMPDEST, pushAt 2478 2 1876, opAt 2479 .JUMP]

def fallback : List Located :=
  [opAt 2480 .JUMPDEST, opAt 2481 (.Dup ⟨0, by decide⟩),
   pushAt 2482 2 4096, pushAt 2483 2 1024, opAt 2484 .MCOPY,
   pushAt 2485 0 0, pushAt 2486 2 1769, opAt 2487 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3395 = true :=
  Artifact.isValidJumpDest_index 2418 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3434 = true :=
  Artifact.isValidJumpDest_index 2443 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3455 = true :=
  Artifact.isValidJumpDest_index 2455 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3456 = true :=
  Artifact.isValidJumpDest_index 2456 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3473 = true :=
  Artifact.isValidJumpDest_index 2463 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3500 = true :=
  Artifact.isValidJumpDest_index 2477 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3505 = true :=
  Artifact.isValidJumpDest_index 2480 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
