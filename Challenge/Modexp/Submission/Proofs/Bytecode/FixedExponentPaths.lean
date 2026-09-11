import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the fixed-exponent dispatcher

The inherited program ends at pc 3694.  The appended handler occupies
pc 3695..3824 and instruction indices 2414..2499.  These definitions are the
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
      [3257,3258,3261,3262,3263,3264,3266,3267,3268,3269,3270,3271,3272,
       3274,3275,3276,3277,3278,3279,3280,3281,3282,3284,3285,
       3286,3287,3288,3290,3291,3292,3294,3295,3298,3299,3302,
       3305,3306][i - 2407]! := by
  interval_cases i <;> decide

@[simp] theorem fixedPC1 (i : Nat) (hi : 2444 ≤ i) (hii : i ≤ 2492) :
    Artifact.submissionArtifact.instructionPC i =
      [3307,3309,3310,3311,3313,3314,3315,3317,3318,3319,3321,3322,3323,
       3324,3325,3328,3329,3330,3331,3332,3333,3334,3335,3337,
       3338,3339,3340,3343,3344,3345,3347,3350,3351,3354,3357,
       3360,3363,3366,3367,3368,3371,3374,3377,3380,3383,3384,
       3385,3386,3388][i - 2444]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2407 .JUMPDEST, opAt 2408 (.Dup ⟨3, by decide⟩),
   pushAt 2409 1 3, opAt 2410 .EQ, pushAt 2411 2 3734,
   opAt 2412 .JUMPI]

def oneWidth : List Located :=
  [opAt 2413 (.Dup ⟨3, by decide⟩), pushAt 2414 1 1,
   opAt 2415 .EQ, opAt 2416 .ISZERO, pushAt 2417 0 0,
   opAt 2418 .JUMPI]

def checkThree : List Located :=
  [pushAt 2419 1 32, opAt 2420 .MLOAD, opAt 2421 .CALLDATALOAD,
   pushAt 2422 0 0, opAt 2423 .BYTE, pushAt 2424 1 3,
   opAt 2425 .EQ, opAt 2426 .ISZERO, pushAt 2427 2 3811,
   opAt 2428 .JUMPI]

def threeHit : List Located :=
  [pushAt 2429 1 1, pushAt 2430 2 3755, opAt 2431 .JUMP]

def check65537 : List Located :=
  [opAt 2432 .JUMPDEST, pushAt 2433 1 32, opAt 2434 .MLOAD,
   opAt 2435 .CALLDATALOAD, pushAt 2436 1 0, opAt 2437 .SHR,
   pushAt 2438 2 9344, opAt 2439 .EQ, opAt 2440 .ISZERO,
   pushAt 2441 2 6144, opAt 2442 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2443 1 16]

def start : List Located :=
  [opAt 2444 .JUMPDEST, opAt 2445 (.Dup ⟨1, by decide⟩),
   pushAt 2446 2 2048, pushAt 2447 1 7, opAt 2448 .MCOPY]

def squareCall : List Located :=
  [opAt 2449 .JUMPDEST, pushAt 2450 1 15, pushAt 2451 2 1024,
   pushAt 2452 2 1024, pushAt 2453 1 31, pushAt 2454 2 1930,
   opAt 2455 .JUMP]

def squareReturn : List Located :=
  [opAt 2456 .JUMPDEST, pushAt 2457 1 1, opAt 2458 (.Swap ⟨0, by decide⟩),
   opAt 2459 .SUB, opAt 2460 (.Dup ⟨0, by decide⟩),
   pushAt 2461 2 3764, opAt 2462 .JUMPI]

def product : List Located :=
  [opAt 2463 .POP, pushAt 2464 0 0, pushAt 2465 2 1024,
   pushAt 2466 1 255, pushAt 2467 2 1024, pushAt 2468 2 1930,
   opAt 2469 .JUMP]

def decode : List Located :=
  [opAt 2470 .JUMPDEST, pushAt 2471 1 1,
   opAt 2472 (.Dup ⟨1, by decide⟩), pushAt 2473 1 96,
   opAt 2474 .ADD, opAt 2475 .MSTORE, pushAt 2476 2 1746,
   pushAt 2477 2 2048, pushAt 2478 2 1024, pushAt 2479 2 6144,
   pushAt 2480 2 4425, opAt 2481 .JUMP]

def finish : List Located :=
  [opAt 2482 .JUMPDEST, pushAt 2483 2 1746, opAt 2484 .JUMP]

def fallback : List Located :=
  [opAt 2485 .JUMPDEST, opAt 2486 (.Dup ⟨0, by decide⟩),
   pushAt 2487 2 4425, pushAt 2488 2 1024, opAt 2489 .MCOPY,
   pushAt 2490 0 0, pushAt 2491 1 31, opAt 2492 .JUMP]

theorem jumpDest3659 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3659 = true :=
  Artifact.isValidJumpDest_index 2407 (by rfl)

theorem jumpDest3698 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3698 = true :=
  Artifact.isValidJumpDest_index 2432 (by rfl)

theorem jumpDest3719 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3719 = true :=
  Artifact.isValidJumpDest_index 2444 (by rfl)

theorem jumpDest3764 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3764 = true :=
  Artifact.isValidJumpDest_index 2449 (by rfl)

theorem jumpDest3781 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3785 = true :=
  Artifact.isValidJumpDest_index 2456 (by rfl)

theorem jumpDest3772 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3772 = true :=
  Artifact.isValidJumpDest_index 2470 (by rfl)

theorem jumpDest3833 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3837 = true :=
  Artifact.isValidJumpDest_index 2482 (by rfl)

theorem jumpDest3802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3806 = true :=
  Artifact.isValidJumpDest_index 2485 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths
