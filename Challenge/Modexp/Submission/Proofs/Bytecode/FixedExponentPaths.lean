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

@[simp] theorem fixedPC0 (i : Nat) (hi : 2407 ≤ i) (hii : i ≤ 2443) :
    Artifact.submissionArtifact.instructionPC i =
      [3695,3696,3698,3699,3700,3701,3703,3704,3706,3707,3708,3709,3710,
       3712,3713,3714,3715,3716,3717,3718,3719,3720,3721,3723,
       3724,3726,3727,3728,3729,3730,3732,3733,3734,3735,3736,
       3737,3738][i - 2407]! := by
  interval_cases i <;> decide

@[simp] theorem fixedPC1 (i : Nat) (hi : 2444 ≤ i) (hii : i ≤ 2492) :
    Artifact.submissionArtifact.instructionPC i =
      [3739,3740,3741,3743,3744,3746,3747,3748,3749,3750,3752,3753,3754,
       3755,3756,3757,3758,3759,3760,3761,3763,3764,3766,3767,
       3768,3769,3770,3772,3773,3774,3775,3776,3777,3778,3779,
       3780,3781,3783,3784,3786,3787,3788,3789,3790,3792,3793,
       3794,3795,3796][i - 2444]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2407 .JUMPDEST, opAt 2408 (.Dup ⟨3, by decide⟩),
   pushAt 2409 1 3, opAt 2410 .EQ, pushAt 2411 2 3734,
   opAt 2412 .JUMPI]

def oneWidth : List Located :=
  [opAt 2413 (.Dup ⟨3, by decide⟩), pushAt 2414 1 1,
   opAt 2415 .EQ, opAt 2416 .ISZERO, pushAt 2417 2 3838,
   opAt 2418 .JUMPI]

def checkThree : List Located :=
  [pushAt 2419 2 9472, opAt 2420 .MLOAD, opAt 2421 .CALLDATALOAD,
   pushAt 2422 0 0, opAt 2423 .BYTE, pushAt 2424 1 3,
   opAt 2425 .EQ, opAt 2426 .ISZERO, pushAt 2427 2 3838,
   opAt 2428 .JUMPI]

def threeHit : List Located :=
  [pushAt 2429 1 1, pushAt 2430 2 3755, opAt 2431 .JUMP]

def check65537 : List Located :=
  [opAt 2432 .JUMPDEST, pushAt 2433 2 9472, opAt 2434 .MLOAD,
   opAt 2435 .CALLDATALOAD, pushAt 2436 1 232, opAt 2437 .SHR,
   pushAt 2438 3 65537, opAt 2439 .EQ, opAt 2440 .ISZERO,
   pushAt 2441 2 3838, opAt 2442 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2443 1 16]

def start : List Located :=
  [opAt 2444 .JUMPDEST, opAt 2445 (.Dup ⟨1, by decide⟩),
   pushAt 2446 2 2048, pushAt 2447 2 1024, opAt 2448 .MCOPY]

def squareCall : List Located :=
  [opAt 2449 .JUMPDEST, pushAt 2450 2 3781, pushAt 2451 2 1024,
   pushAt 2452 2 1024, pushAt 2453 2 1024, pushAt 2454 2 1939,
   opAt 2455 .JUMP]

def squareReturn : List Located :=
  [opAt 2456 .JUMPDEST, pushAt 2457 1 1, opAt 2458 (.Swap ⟨0, by decide⟩),
   opAt 2459 .SUB, opAt 2460 (.Dup ⟨0, by decide⟩),
   pushAt 2461 2 3764, opAt 2462 .JUMPI]

def product : List Located :=
  [opAt 2463 .POP, pushAt 2464 2 3808, pushAt 2465 2 1024,
   pushAt 2466 2 2048, pushAt 2467 2 1024, pushAt 2468 2 1939,
   opAt 2469 .JUMP]

def decode : List Located :=
  [opAt 2470 .JUMPDEST, pushAt 2471 1 1,
   opAt 2472 (.Dup ⟨1, by decide⟩), pushAt 2473 2 3040,
   opAt 2474 .ADD, opAt 2475 .MSTORE, pushAt 2476 2 3833,
   pushAt 2477 2 1024, pushAt 2478 2 3072, pushAt 2479 2 1024,
   pushAt 2480 2 1939, opAt 2481 .JUMP]

def finish : List Located :=
  [opAt 2482 .JUMPDEST, pushAt 2483 2 1876, opAt 2484 .JUMP]

def fallback : List Located :=
  [opAt 2485 .JUMPDEST, opAt 2486 (.Dup ⟨0, by decide⟩),
   pushAt 2487 2 4096, pushAt 2488 2 1024, opAt 2489 .MCOPY,
   pushAt 2490 0 0, pushAt 2491 2 1769, opAt 2492 .JUMP]

theorem jumpDest3695 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3695 = true :=
  Artifact.isValidJumpDest_index 2407 (by rfl)

theorem jumpDest3734 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3734 = true :=
  Artifact.isValidJumpDest_index 2432 (by rfl)

theorem jumpDest3755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3755 = true :=
  Artifact.isValidJumpDest_index 2444 (by rfl)

theorem jumpDest3764 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3764 = true :=
  Artifact.isValidJumpDest_index 2449 (by rfl)

theorem jumpDest3781 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3781 = true :=
  Artifact.isValidJumpDest_index 2456 (by rfl)

theorem jumpDest3808 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3808 = true :=
  Artifact.isValidJumpDest_index 2470 (by rfl)

theorem jumpDest3833 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3833 = true :=
  Artifact.isValidJumpDest_index 2482 (by rfl)

theorem jumpDest3838 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3838 = true :=
  Artifact.isValidJumpDest_index 2485 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths
