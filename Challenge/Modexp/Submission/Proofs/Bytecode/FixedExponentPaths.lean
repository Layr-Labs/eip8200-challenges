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

@[simp] theorem fixedPC0 (i : Nat) (hi : 2405 ≤ i) (hii : i ≤ 2441) :
    Artifact.submissionArtifact.instructionPC i =
      [3695,3696,3698,3699,3700,3701,3703,3704,3706,3707,3708,3709,3710,
       3712,3713,3714,3715,3716,3717,3718,3719,3720,3721,3723,
       3724,3726,3727,3728,3729,3730,3732,3733,3734,3735,3736,
       3737,3738][i - 2405]! := by
  interval_cases i <;> decide

@[simp] theorem fixedPC1 (i : Nat) (hi : 2442 ≤ i) (hii : i ≤ 2490) :
    Artifact.submissionArtifact.instructionPC i =
      [3739,3740,3741,3743,3744,3746,3747,3748,3749,3750,3752,3753,3754,
       3755,3756,3757,3758,3759,3760,3761,3763,3764,3766,3767,
       3768,3769,3770,3772,3773,3774,3775,3776,3777,3778,3779,
       3780,3781,3783,3784,3786,3787,3788,3789,3790,3792,3793,
       3794,3795,3796][i - 2442]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2405 .JUMPDEST, opAt 2406 (.Dup ⟨3, by decide⟩),
   pushAt 2407 1 3, opAt 2408 .EQ, pushAt 2409 2 3734,
   opAt 2410 .JUMPI]

def oneWidth : List Located :=
  [opAt 2411 (.Dup ⟨3, by decide⟩), pushAt 2412 1 1,
   opAt 2413 .EQ, opAt 2414 .ISZERO, pushAt 2415 2 3838,
   opAt 2416 .JUMPI]

def checkThree : List Located :=
  [pushAt 2417 2 9472, opAt 2418 .MLOAD, opAt 2419 .CALLDATALOAD,
   pushAt 2420 0 0, opAt 2421 .BYTE, pushAt 2422 1 3,
   opAt 2423 .EQ, opAt 2424 .ISZERO, pushAt 2425 2 3838,
   opAt 2426 .JUMPI]

def threeHit : List Located :=
  [pushAt 2427 1 1, pushAt 2428 2 3755, opAt 2429 .JUMP]

def check65537 : List Located :=
  [opAt 2430 .JUMPDEST, pushAt 2431 2 9472, opAt 2432 .MLOAD,
   opAt 2433 .CALLDATALOAD, pushAt 2434 1 232, opAt 2435 .SHR,
   pushAt 2436 3 65537, opAt 2437 .EQ, opAt 2438 .ISZERO,
   pushAt 2439 2 3838, opAt 2440 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2441 1 16]

def start : List Located :=
  [opAt 2442 .JUMPDEST, opAt 2443 (.Dup ⟨1, by decide⟩),
   pushAt 2444 2 2048, pushAt 2445 2 1024, opAt 2446 .MCOPY]

def squareCall : List Located :=
  [opAt 2447 .JUMPDEST, pushAt 2448 2 3781, pushAt 2449 2 1024,
   pushAt 2450 2 1024, pushAt 2451 2 1024, pushAt 2452 2 1939,
   opAt 2453 .JUMP]

def squareReturn : List Located :=
  [opAt 2454 .JUMPDEST, pushAt 2455 1 1, opAt 2456 (.Swap ⟨0, by decide⟩),
   opAt 2457 .SUB, opAt 2458 (.Dup ⟨0, by decide⟩),
   pushAt 2459 2 3764, opAt 2460 .JUMPI]

def product : List Located :=
  [opAt 2461 .POP, pushAt 2462 2 3808, pushAt 2463 2 1024,
   pushAt 2464 2 2048, pushAt 2465 2 1024, pushAt 2466 2 1939,
   opAt 2467 .JUMP]

def decode : List Located :=
  [opAt 2468 .JUMPDEST, pushAt 2469 1 1,
   opAt 2470 (.Dup ⟨1, by decide⟩), pushAt 2471 2 3040,
   opAt 2472 .ADD, opAt 2473 .MSTORE, pushAt 2474 2 3833,
   pushAt 2475 2 1024, pushAt 2476 2 3072, pushAt 2477 2 1024,
   pushAt 2478 2 1939, opAt 2479 .JUMP]

def finish : List Located :=
  [opAt 2480 .JUMPDEST, pushAt 2481 2 1876, opAt 2482 .JUMP]

def fallback : List Located :=
  [opAt 2483 .JUMPDEST, opAt 2484 (.Dup ⟨0, by decide⟩),
   pushAt 2485 2 4096, pushAt 2486 2 1024, opAt 2487 .MCOPY,
   pushAt 2488 0 0, pushAt 2489 2 1769, opAt 2490 .JUMP]

theorem jumpDest3695 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3695 = true :=
  Artifact.isValidJumpDest_index 2405 (by rfl)

theorem jumpDest3734 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3734 = true :=
  Artifact.isValidJumpDest_index 2430 (by rfl)

theorem jumpDest3755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3755 = true :=
  Artifact.isValidJumpDest_index 2442 (by rfl)

theorem jumpDest3764 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3764 = true :=
  Artifact.isValidJumpDest_index 2447 (by rfl)

theorem jumpDest3781 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3781 = true :=
  Artifact.isValidJumpDest_index 2454 (by rfl)

theorem jumpDest3808 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3808 = true :=
  Artifact.isValidJumpDest_index 2468 (by rfl)

theorem jumpDest3833 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3833 = true :=
  Artifact.isValidJumpDest_index 2480 (by rfl)

theorem jumpDest3838 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3838 = true :=
  Artifact.isValidJumpDest_index 2483 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths
