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

@[simp] theorem fixedPC0 (i : Nat) (hi : 2398 ≤ i) (hii : i ≤ 2434) :
    Artifact.submissionArtifact.instructionPC i =
      [3695,3696,3698,3699,3700,3701,3703,3704,3706,3707,3708,3709,3710,
       3712,3713,3714,3715,3716,3717,3718,3719,3720,3721,3723,
       3724,3726,3727,3728,3729,3730,3732,3733,3734,3735,3736,
       3737,3738][i - 2398]! := by
  interval_cases i <;> decide

@[simp] theorem fixedPC1 (i : Nat) (hi : 2435 ≤ i) (hii : i ≤ 2483) :
    Artifact.submissionArtifact.instructionPC i =
      [3739,3740,3741,3743,3744,3746,3747,3748,3749,3750,3752,3753,3754,
       3755,3756,3757,3758,3759,3760,3761,3763,3764,3766,3767,
       3768,3769,3770,3772,3773,3774,3775,3776,3777,3778,3779,
       3780,3781,3783,3784,3786,3787,3788,3789,3790,3792,3793,
       3794,3795,3796][i - 2435]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2398 .JUMPDEST, opAt 2399 (.Dup ⟨3, by decide⟩),
   pushAt 2400 1 3, opAt 2401 .EQ, pushAt 2402 2 3734,
   opAt 2403 .JUMPI]

def oneWidth : List Located :=
  [opAt 2404 (.Dup ⟨3, by decide⟩), pushAt 2405 1 1,
   opAt 2406 .EQ, opAt 2407 .ISZERO, pushAt 2408 2 3838,
   opAt 2409 .JUMPI]

def checkThree : List Located :=
  [pushAt 2410 2 9472, opAt 2411 .MLOAD, opAt 2412 .CALLDATALOAD,
   pushAt 2413 0 0, opAt 2414 .BYTE, pushAt 2415 1 3,
   opAt 2416 .EQ, opAt 2417 .ISZERO, pushAt 2418 2 3838,
   opAt 2419 .JUMPI]

def threeHit : List Located :=
  [pushAt 2420 1 1, pushAt 2421 2 3755, opAt 2422 .JUMP]

def check65537 : List Located :=
  [opAt 2423 .JUMPDEST, pushAt 2424 2 9472, opAt 2425 .MLOAD,
   opAt 2426 .CALLDATALOAD, pushAt 2427 1 232, opAt 2428 .SHR,
   pushAt 2429 3 65537, opAt 2430 .EQ, opAt 2431 .ISZERO,
   pushAt 2432 2 3838, opAt 2433 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2434 1 16]

def start : List Located :=
  [opAt 2435 .JUMPDEST, opAt 2436 (.Dup ⟨1, by decide⟩),
   pushAt 2437 2 2048, pushAt 2438 2 1024, opAt 2439 .MCOPY]

def squareCall : List Located :=
  [opAt 2440 .JUMPDEST, pushAt 2441 2 3781, pushAt 2442 2 1024,
   pushAt 2443 2 1024, pushAt 2444 2 1024, pushAt 2445 2 1939,
   opAt 2446 .JUMP]

def squareReturn : List Located :=
  [opAt 2447 .JUMPDEST, pushAt 2448 1 1, opAt 2449 (.Swap ⟨0, by decide⟩),
   opAt 2450 .SUB, opAt 2451 (.Dup ⟨0, by decide⟩),
   pushAt 2452 2 3764, opAt 2453 .JUMPI]

def product : List Located :=
  [opAt 2454 .POP, pushAt 2455 2 3808, pushAt 2456 2 1024,
   pushAt 2457 2 2048, pushAt 2458 2 1024, pushAt 2459 2 1939,
   opAt 2460 .JUMP]

def decode : List Located :=
  [opAt 2461 .JUMPDEST, pushAt 2462 1 1,
   opAt 2463 (.Dup ⟨1, by decide⟩), pushAt 2464 2 3040,
   opAt 2465 .ADD, opAt 2466 .MSTORE, pushAt 2467 2 3833,
   pushAt 2468 2 1024, pushAt 2469 2 3072, pushAt 2470 2 1024,
   pushAt 2471 2 1939, opAt 2472 .JUMP]

def finish : List Located :=
  [opAt 2473 .JUMPDEST, pushAt 2474 2 1876, opAt 2475 .JUMP]

def fallback : List Located :=
  [opAt 2476 .JUMPDEST, opAt 2477 (.Dup ⟨0, by decide⟩),
   pushAt 2478 2 4096, pushAt 2479 2 1024, opAt 2480 .MCOPY,
   pushAt 2481 0 0, pushAt 2482 2 1769, opAt 2483 .JUMP]

theorem jumpDest3695 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3695 = true :=
  Artifact.isValidJumpDest_index 2398 (by rfl)

theorem jumpDest3734 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3734 = true :=
  Artifact.isValidJumpDest_index 2423 (by rfl)

theorem jumpDest3755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3755 = true :=
  Artifact.isValidJumpDest_index 2435 (by rfl)

theorem jumpDest3764 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3764 = true :=
  Artifact.isValidJumpDest_index 2440 (by rfl)

theorem jumpDest3781 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3781 = true :=
  Artifact.isValidJumpDest_index 2447 (by rfl)

theorem jumpDest3808 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3808 = true :=
  Artifact.isValidJumpDest_index 2461 (by rfl)

theorem jumpDest3833 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3833 = true :=
  Artifact.isValidJumpDest_index 2473 (by rfl)

theorem jumpDest3838 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3838 = true :=
  Artifact.isValidJumpDest_index 2476 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths
