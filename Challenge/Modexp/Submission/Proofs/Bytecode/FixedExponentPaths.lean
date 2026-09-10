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

@[simp] theorem fixedPC0 (i : Nat) (hi : 2403 ≤ i) (hii : i ≤ 2439) :
    Artifact.submissionArtifact.instructionPC i =
      [3257,3258,3261,3262,3263,3264,3266,3267,3268,3269,3270,3271,3272,3274,3275,3276,3277,3278,3279,3280,3281,3282,3284,3285,3286,3287,3288,3290,3291,3292,3294,3295,3298,3299,3302,3305,3306][i - 2403]! := by
  interval_cases i <;> decide

@[simp] theorem fixedPC1 (i : Nat) (hi : 2440 ≤ i) (hii : i ≤ 2488) :
    Artifact.submissionArtifact.instructionPC i =
      [3307,3309,3310,3311,3313,3314,3315,3317,3318,3319,3321,3322,3323,3324,3325,3328,3329,3330,3331,3332,3333,3334,3335,3337,3338,3339,3340,3343,3344,3345,3347,3350,3351,3354,3357,3360,3363,3366,3367,3368,3371,3374,3377,3380,3383,3384,3385,3386,3388][i - 2440]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2403 .JUMPDEST, opAt 2404 (.Dup ⟨3, by decide⟩),
   pushAt 2405 1 3, opAt 2406 .EQ, pushAt 2407 2 3734,
   opAt 2408 .JUMPI]

def oneWidth : List Located :=
  [opAt 2409 (.Dup ⟨3, by decide⟩), pushAt 2410 1 1,
   opAt 2411 .EQ, opAt 2412 .ISZERO, pushAt 2413 0 0,
   opAt 2414 .JUMPI]

def checkThree : List Located :=
  [pushAt 2415 1 32, opAt 2416 .MLOAD, opAt 2417 .CALLDATALOAD,
   pushAt 2418 0 0, opAt 2419 .BYTE, pushAt 2420 1 3,
   opAt 2421 .EQ, opAt 2422 .ISZERO, pushAt 2423 2 3838,
   opAt 2424 .JUMPI]

def threeHit : List Located :=
  [pushAt 2425 1 1, pushAt 2426 2 3755, opAt 2427 .JUMP]

def check65537 : List Located :=
  [opAt 2428 .JUMPDEST, pushAt 2429 1 32, opAt 2430 .MLOAD,
   opAt 2431 .CALLDATALOAD, pushAt 2432 1 0, opAt 2433 .SHR,
   pushAt 2434 2 9344, opAt 2435 .EQ, opAt 2436 .ISZERO,
   pushAt 2437 2 6144, opAt 2438 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2439 1 16]

def start : List Located :=
  [opAt 2440 .JUMPDEST, opAt 2441 (.Dup ⟨1, by decide⟩),
   pushAt 2442 2 2048, pushAt 2443 1 7, opAt 2444 .MCOPY]

def squareCall : List Located :=
  [opAt 2445 .JUMPDEST, pushAt 2446 1 15, pushAt 2447 2 1024,
   pushAt 2448 2 1024, pushAt 2449 1 31, pushAt 2450 2 1930,
   opAt 2451 .JUMP]

def squareReturn : List Located :=
  [opAt 2452 .JUMPDEST, pushAt 2453 1 1, opAt 2454 (.Swap ⟨0, by decide⟩),
   opAt 2455 .SUB, opAt 2456 (.Dup ⟨0, by decide⟩),
   pushAt 2457 2 3764, opAt 2458 .JUMPI]

def product : List Located :=
  [opAt 2459 .POP, pushAt 2460 0 0, pushAt 2461 2 1024,
   pushAt 2462 1 255, pushAt 2463 2 1024, pushAt 2464 2 1930,
   opAt 2465 .JUMP]

def decode : List Located :=
  [opAt 2466 .JUMPDEST, pushAt 2467 1 1,
   opAt 2468 (.Dup ⟨1, by decide⟩), pushAt 2469 1 96,
   opAt 2470 .ADD, opAt 2471 .MSTORE, pushAt 2472 2 1746,
   pushAt 2473 2 2048, pushAt 2474 2 1024, pushAt 2475 2 6144,
   pushAt 2476 2 4428, opAt 2477 .JUMP]

def finish : List Located :=
  [opAt 2478 .JUMPDEST, pushAt 2479 2 1746, opAt 2480 .JUMP]

def fallback : List Located :=
  [opAt 2481 .JUMPDEST, opAt 2482 (.Dup ⟨0, by decide⟩),
   pushAt 2483 2 4428, pushAt 2484 2 1024, opAt 2485 .MCOPY,
   pushAt 2486 0 0, pushAt 2487 1 31, opAt 2488 .JUMP]

theorem jumpDest3659 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3659 = true :=
  Artifact.isValidJumpDest_index 2403 (by rfl)

theorem jumpDest3698 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3698 = true :=
  Artifact.isValidJumpDest_index 2428 (by rfl)

theorem jumpDest3719 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3719 = true :=
  Artifact.isValidJumpDest_index 2440 (by rfl)

theorem jumpDest3764 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3764 = true :=
  Artifact.isValidJumpDest_index 2445 (by rfl)

theorem jumpDest3781 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3781 = true :=
  Artifact.isValidJumpDest_index 2452 (by rfl)

theorem jumpDest3772 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3772 = true :=
  Artifact.isValidJumpDest_index 2466 (by rfl)

theorem jumpDest3833 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3833 = true :=
  Artifact.isValidJumpDest_index 2478 (by rfl)

theorem jumpDest3802 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3802 = true :=
  Artifact.isValidJumpDest_index 2481 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths
