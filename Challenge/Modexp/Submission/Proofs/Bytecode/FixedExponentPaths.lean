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
  [opAt 2414 .JUMPDEST, opAt 2415 (.Dup ⟨3, by decide⟩),
   pushAt 2416 1 3, opAt 2417 .EQ, pushAt 2418 2 3734,
   opAt 2419 .JUMPI]

def oneWidth : List Located :=
  [opAt 2420 (.Dup ⟨3, by decide⟩), pushAt 2421 1 1,
   opAt 2422 .EQ, opAt 2423 .ISZERO, pushAt 2424 2 3838,
   opAt 2425 .JUMPI]

def checkThree : List Located :=
  [pushAt 2426 2 9472, opAt 2427 .MLOAD, opAt 2428 .CALLDATALOAD,
   pushAt 2429 0 0, opAt 2430 .BYTE, pushAt 2431 1 3,
   opAt 2432 .EQ, opAt 2433 .ISZERO, pushAt 2434 2 3838,
   opAt 2435 .JUMPI]

def threeHit : List Located :=
  [pushAt 2436 1 1, pushAt 2437 2 3755, opAt 2438 .JUMP]

def check65537 : List Located :=
  [opAt 2439 .JUMPDEST, pushAt 2440 2 9472, opAt 2441 .MLOAD,
   opAt 2442 .CALLDATALOAD, pushAt 2443 1 232, opAt 2444 .SHR,
   pushAt 2445 2 1569, opAt 2446 .EQ, opAt 2447 .ISZERO,
   pushAt 2448 2 3838, opAt 2449 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2450 1 16]

def start : List Located :=
  [opAt 2451 .JUMPDEST, opAt 2452 (.Dup ⟨1, by decide⟩),
   pushAt 2453 2 2048, pushAt 2454 2 1024, opAt 2455 .MCOPY]

def squareCall : List Located :=
  [opAt 2456 .JUMPDEST, pushAt 2457 2 3420, pushAt 2458 2 1024,
   pushAt 2459 2 1024, pushAt 2460 2 1024, pushAt 2461 2 1939,
   opAt 2462 .JUMP]

def squareReturn : List Located :=
  [opAt 2463 .JUMPDEST, pushAt 2464 1 1, opAt 2465 (.Swap ⟨0, by decide⟩),
   opAt 2466 .SUB, opAt 2467 (.Dup ⟨0, by decide⟩),
   pushAt 2468 2 3764, opAt 2469 .JUMPI]

def product : List Located :=
  [opAt 2470 .POP, pushAt 2471 2 3808, pushAt 2472 2 1024,
   pushAt 2473 2 2048, pushAt 2474 2 4458, pushAt 2475 2 1939,
   opAt 2476 .JUMP]

def decode : List Located :=
  [opAt 2477 .JUMPDEST, pushAt 2478 1 1,
   opAt 2479 (.Dup ⟨1, by decide⟩), pushAt 2480 2 3040,
   opAt 2481 .ADD, opAt 2482 .MSTORE, pushAt 2483 2 3833,
   pushAt 2484 2 1024, pushAt 2485 2 3072, pushAt 2486 2 1024,
   pushAt 2487 2 1939, opAt 2488 .JUMP]

def finish : List Located :=
  [opAt 2489 .JUMPDEST, pushAt 2490 2 1876, opAt 2491 .JUMP]

def fallback : List Located :=
  [opAt 2492 .JUMPDEST, opAt 2493 (.Dup ⟨0, by decide⟩),
   pushAt 2494 2 4096, pushAt 2495 2 1024, opAt 2496 .MCOPY,
   pushAt 2497 0 0, pushAt 2498 2 1668, opAt 2499 .JUMP]

theorem jumpDest3695 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3695 = true :=
  Artifact.isValidJumpDest_index 2414 (by rfl)

theorem jumpDest3734 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3734 = true :=
  Artifact.isValidJumpDest_index 2439 (by rfl)

theorem jumpDest3755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3755 = true :=
  Artifact.isValidJumpDest_index 2451 (by rfl)

theorem jumpDest3764 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3764 = true :=
  Artifact.isValidJumpDest_index 2456 (by rfl)

theorem jumpDest3781 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3781 = true :=
  Artifact.isValidJumpDest_index 2463 (by rfl)

theorem jumpDest3808 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3808 = true :=
  Artifact.isValidJumpDest_index 2477 (by rfl)

theorem jumpDest3833 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3833 = true :=
  Artifact.isValidJumpDest_index 2489 (by rfl)

theorem jumpDest3838 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3838 = true :=
  Artifact.isValidJumpDest_index 2492 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths
