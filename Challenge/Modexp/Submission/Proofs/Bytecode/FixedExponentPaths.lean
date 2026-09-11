import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the fixed-exponent dispatcher

The inherited program ends at pc 3694.  The appended handler occupies
pc 3695..3820 and instruction indices 2414..2499.  These definitions are the
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
      [3257,3258,3261,3262,3263,3264,3266,3267,3268,3269,3270,3271,3272,
       3274,3275,3276,3277,3278,3279,3280,3281,3282,3284,3285,
       3286,3287,3288,3290,3291,3292,3294,3295,3298,3299,3302,
       3305,3306][i - 2405]! := by
  interval_cases i <;> decide

@[simp] theorem fixedPC1 (i : Nat) (hi : 2442 ≤ i) (hii : i ≤ 2490) :
    Artifact.submissionArtifact.instructionPC i =
      [3307,3309,3310,3311,3313,3314,3315,3317,3318,3319,3321,3322,3323,
       3324,3325,3328,3329,3330,3331,3332,3333,3334,3335,3337,
       3338,3339,3340,3343,3344,3345,3347,3350,3351,3354,3357,
       3360,3363,3366,3367,3368,3371,3374,3377,3380,3383,3384,
       3385,3386,3388][i - 2442]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2405 .JUMPDEST, opAt 2406 (.Dup ⟨3, by decide⟩),
   pushAt 2407 1 3, opAt 2408 .EQ, pushAt 2409 2 3734,
   opAt 2410 .JUMPI]

def oneWidth : List Located :=
  [opAt 2411 (.Dup ⟨3, by decide⟩), pushAt 2412 1 1,
   opAt 2413 .EQ, opAt 2414 .ISZERO, pushAt 2415 0 0,
   opAt 2416 .JUMPI]

def checkThree : List Located :=
  [pushAt 2417 1 32, opAt 2418 .MLOAD, opAt 2419 .CALLDATALOAD,
   pushAt 2420 0 0, opAt 2421 .BYTE, pushAt 2422 1 3,
   opAt 2423 .EQ, opAt 2424 .ISZERO, pushAt 2425 2 3807,
   opAt 2426 .JUMPI]

def threeHit : List Located :=
  [pushAt 2427 1 1, pushAt 2428 2 3755, opAt 2429 .JUMP]

def check65537 : List Located :=
  [opAt 2430 .JUMPDEST, pushAt 2431 1 32, opAt 2432 .MLOAD,
   opAt 2433 .CALLDATALOAD, pushAt 2434 1 0, opAt 2435 .SHR,
   pushAt 2436 2 9344, opAt 2437 .EQ, opAt 2438 .ISZERO,
   pushAt 2439 2 6144, opAt 2440 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2441 1 16]

def start : List Located :=
  [opAt 2442 .JUMPDEST, opAt 2443 (.Dup ⟨1, by decide⟩),
   pushAt 2444 2 2048, pushAt 2445 1 7, opAt 2446 .MCOPY]

def squareCall : List Located :=
  [opAt 2447 .JUMPDEST, pushAt 2448 1 15, pushAt 2449 2 1024,
   pushAt 2450 2 1024, pushAt 2451 1 31, pushAt 2452 2 1930,
   opAt 2453 .JUMP]

def squareReturn : List Located :=
  [opAt 2454 .JUMPDEST, pushAt 2455 1 1, opAt 2456 (.Swap ⟨0, by decide⟩),
   opAt 2457 .SUB, opAt 2458 (.Dup ⟨0, by decide⟩),
   pushAt 2459 2 3764, opAt 2460 .JUMPI]

def product : List Located :=
  [opAt 2461 .POP, pushAt 2462 0 0, pushAt 2463 2 1024,
   pushAt 2464 1 255, pushAt 2465 2 1024, pushAt 2466 2 1930,
   opAt 2467 .JUMP]

def decode : List Located :=
  [opAt 2468 .JUMPDEST, pushAt 2469 1 1,
   opAt 2470 (.Dup ⟨1, by decide⟩), pushAt 2471 1 96,
   opAt 2472 .ADD, opAt 2473 .MSTORE, pushAt 2474 2 1746,
   pushAt 2475 2 2048, pushAt 2476 2 1024, pushAt 2477 2 6144,
   pushAt 2478 2 4416, opAt 2479 .JUMP]

def finish : List Located :=
  [opAt 2480 .JUMPDEST, pushAt 2481 2 1746, opAt 2482 .JUMP]

def fallback : List Located :=
  [opAt 2483 .JUMPDEST, opAt 2484 (.Dup ⟨0, by decide⟩),
   pushAt 2485 2 4416, pushAt 2486 2 1024, opAt 2487 .MCOPY,
   pushAt 2488 0 0, pushAt 2489 1 31, opAt 2490 .JUMP]

theorem jumpDest3659 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3659 = true :=
  Artifact.isValidJumpDest_index 2405 (by rfl)

theorem jumpDest3698 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3698 = true :=
  Artifact.isValidJumpDest_index 2430 (by rfl)

theorem jumpDest3719 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3719 = true :=
  Artifact.isValidJumpDest_index 2442 (by rfl)

theorem jumpDest3764 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3764 = true :=
  Artifact.isValidJumpDest_index 2447 (by rfl)

theorem jumpDest3781 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3781 = true :=
  Artifact.isValidJumpDest_index 2454 (by rfl)

theorem jumpDest3772 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3772 = true :=
  Artifact.isValidJumpDest_index 2468 (by rfl)

theorem jumpDest3833 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3833 = true :=
  Artifact.isValidJumpDest_index 2480 (by rfl)

theorem jumpDest3802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3802 = true :=
  Artifact.isValidJumpDest_index 2483 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths
