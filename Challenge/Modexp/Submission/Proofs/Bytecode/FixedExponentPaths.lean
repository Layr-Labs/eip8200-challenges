import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the fixed-exponent dispatcher

The inherited program ends at pc 3694.  The appended handler occupies
pc 3695..3851 and instruction indices 2414..2499.  These definitions are the
artifact-dependent boundary of the fixed-exponent proof; the regenerated
artifact must discharge the PC and jump-destination certificates below.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem fixedPC0 (i : Nat) (hi : 2414 ≤ i) (hii : i ≤ 2450) :
    Artifact.submissionArtifact.instructionPC i =
      [3695,3696,3698,3699,3700,3701,3703,3704,3706,3707,3708,3709,3710,
       3712,3713,3714,3715,3716,3717,3718,3719,3720,3721,3723,
       3724,3726,3727,3728,3729,3730,3732,3733,3734,3735,3736,
       3737,3738][i - 2414]! := by
  interval_cases i <;> decide

@[simp] theorem fixedPC1 (i : Nat) (hi : 2451 ≤ i) (hii : i ≤ 2499) :
    Artifact.submissionArtifact.instructionPC i =
      [3739,3740,3741,3743,3744,3746,3747,3748,3749,3750,3752,3753,3754,
       3755,3756,3757,3758,3759,3760,3761,3763,3764,3766,3767,
       3768,3769,3770,3772,3773,3774,3775,3776,3777,3778,3779,
       3780,3781,3783,3784,3786,3787,3788,3789,3790,3792,3793,
       3794,3795,3796][i - 2451]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2413 .JUMPDEST, opAt 2414 (.Dup ⟨3, by decide⟩),
   pushAt 2415 -8 0, opAt 2416 .EQ, pushAt 2417 -13 0,
   opAt 2418 .JUMPI]

def oneWidth : List Located :=
  [opAt 2419 (.Dup ⟨3, by decide⟩), pushAt 2420 148 0,
   opAt 2421 .EQ, opAt 2422 .ISZERO, pushAt 2423 0 0,
   opAt 2424 .JUMPI]

def checkThree : List Located :=
  [pushAt 2425 1 32, opAt 2426 .MLOAD, opAt 2427 .CALLDATALOAD,
   pushAt 2428 -4 0, opAt 2429 .BYTE, pushAt 2430 -42 0,
   opAt 2431 .EQ, opAt 2432 .ISZERO, pushAt 2433 -42 0,
   opAt 2434 .JUMPI]

def threeHit : List Located :=
  [pushAt 2435 -89 0, pushAt 2436 -93 0, opAt 2437 .JUMP]

def check65537 : List Located :=
  [opAt 2438 .JUMPDEST, pushAt 2439 1 32, opAt 2440 .MLOAD,
   opAt 2441 .CALLDATALOAD, pushAt 2442 0 0, opAt 2443 .SHR,
   pushAt 2444 2 9344, opAt 2445 .EQ, opAt 2446 .ISZERO,
   pushAt 2447 2 6144, opAt 2448 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2449 34 0]

def start : List Located :=
  [opAt 2450 .JUMPDEST, opAt 2451 (.Dup ⟨1, by decide⟩),
   pushAt 2452 35 0, pushAt 2453 1 7, opAt 2454 .MCOPY]

def squareCall : List Located :=
  [opAt 2455 .JUMPDEST, pushAt 2456 1 15, pushAt 2457 -79 0,
   pushAt 2458 37 0, pushAt 2459 1 31, pushAt 2460 -79 0,
   opAt 2461 .JUMP]

def squareReturn : List Located :=
  [opAt 2462 .JUMPDEST, pushAt 2463 -94 0, opAt 2464 (.Swap ⟨0, by decide⟩),
   opAt 2465 .SUB, opAt 2466 (.Dup ⟨0, by decide⟩),
   pushAt 2467 33 0, opAt 2468 .JUMPI]

def product : List Located :=
  [opAt 2469 .POP, pushAt 2470 0 0, pushAt 2471 -14 0,
   pushAt 2472 1 255, pushAt 2473 -67 0, pushAt 2474 -73 0,
   opAt 2475 .JUMP]

def decode : List Located :=
  [opAt 2476 .JUMPDEST, pushAt 2477 -8 0,
   opAt 2478 (.Dup ⟨1, by decide⟩), pushAt 2479 1 96,
   opAt 2480 .ADD, opAt 2481 .MSTORE, pushAt 2482 2 1736,
   pushAt 2483 2 2048, pushAt 2484 2 1024, pushAt 2485 2 6144,
   pushAt 2486 2 4440, opAt 2487 .JUMP]

def finish : List Located :=
  [opAt 2488 .JUMPDEST, pushAt 2489 2 1736, opAt 2490 .JUMP]

def fallback : List Located :=
  [opAt 2491 .JUMPDEST, opAt 2492 (.Dup ⟨0, by decide⟩),
   pushAt 2493 2 4440, pushAt 2494 -9 0, opAt 2495 .MCOPY,
   pushAt 2496 35 0, pushAt 2497 1 31, opAt 2498 .JUMP]

theorem jumpDest3695 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3678 = true :=
  Artifact.isValidJumpDest_index 2413 (by rfl)

theorem jumpDest3734 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3717 = true :=
  Artifact.isValidJumpDest_index 2438 (by rfl)

theorem jumpDest3755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3738 = true :=
  Artifact.isValidJumpDest_index 2450 (by rfl)

theorem jumpDest3764 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3764 = true :=
  Artifact.isValidJumpDest_index 2455 (by rfl)

theorem jumpDest3781 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3781 = true :=
  Artifact.isValidJumpDest_index 2462 (by rfl)

theorem jumpDest3808 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3791 = true :=
  Artifact.isValidJumpDest_index 2476 (by rfl)

theorem jumpDest3833 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3833 = true :=
  Artifact.isValidJumpDest_index 2488 (by rfl)

theorem jumpDest3838 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3821 = true :=
  Artifact.isValidJumpDest_index 2491 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths
