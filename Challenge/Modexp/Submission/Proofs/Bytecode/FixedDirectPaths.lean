import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The appended handler occupies pc3892..4015 and instruction indices2572..2641.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2474 ≤ i) (hii : i ≤ 2510) :
    Artifact.submissionArtifact.instructionPC i =
      [3810,3811,3812,3814,3815,3818,3819,3820,3822,3823,
       3824,3827,3828,3831,3832,3833,3834,3835,3837,3838,
       3839,3842,3843,3845,3848,3849,3850,3853,3854,3855,
       3857,3858,3862,3863,3864,3867,3868][i - 2474]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2511 ≤ i) (hii : i ≤ 2543) :
    Artifact.submissionArtifact.instructionPC i =
      [3870,3871,3872,3875,3878,3881,3884,3887,3888,3889,
       3891,3892,3893,3894,3897,3898,3899,3902,3905,3908,
       3911,3914,3915,3916,3919,3920,3921,3922,3925,3928,
       3929,3930,3933][i - 2511]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2474 .JUMPDEST, opAt 2475 (.Dup ⟨3, by decide⟩),
   pushAt 2476 1 3, opAt 2477 .EQ, pushAt 2478 2 3849,
   opAt 2479 .JUMPI]

def oneWidth : List Located :=
  [opAt 2480 (.Dup ⟨3, by decide⟩), pushAt 2481 1 1,
   opAt 2482 .EQ, opAt 2483 .ISZERO, pushAt 2484 2 3920,
   opAt 2485 .JUMPI]

def checkThree : List Located :=
  [pushAt 2486 2 9472, opAt 2487 .MLOAD, opAt 2488 .CALLDATALOAD,
   pushAt 2489 0 0, opAt 2490 .BYTE, pushAt 2491 1 3,
   opAt 2492 .EQ, opAt 2493 .ISZERO, pushAt 2494 2 3920,
   opAt 2495 .JUMPI]

def threeHit : List Located :=
  [pushAt 2496 1 1, pushAt 2497 2 3870, opAt 2498 .JUMP]

def check65537 : List Located :=
  [opAt 2499 .JUMPDEST, pushAt 2500 2 9472, opAt 2501 .MLOAD,
   opAt 2502 .CALLDATALOAD, pushAt 2503 1 232, opAt 2504 .SHR,
   pushAt 2505 3 65537, opAt 2506 .EQ, opAt 2507 .ISZERO,
   pushAt 2508 2 3920, opAt 2509 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2510 1 16]

def start : List Located :=
  [opAt 2511 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2512 .JUMPDEST, pushAt 2513 2 3888, pushAt 2514 2 2048,
   pushAt 2515 2 2048, pushAt 2516 2 2048, pushAt 2517 2 1939,
   opAt 2518 .JUMP]

def squareReturn : List Located :=
  [opAt 2519 .JUMPDEST, pushAt 2520 1 1,
   opAt 2521 (.Swap ⟨0, by decide⟩), opAt 2522 .SUB,
   opAt 2523 (.Dup ⟨0, by decide⟩), pushAt 2524 2 3871,
   opAt 2525 .JUMPI]

def product : List Located :=
  [opAt 2526 .POP, pushAt 2527 2 3915, pushAt 2528 2 1024,
   pushAt 2529 2 1024, pushAt 2530 2 2048, pushAt 2531 2 1939,
   opAt 2532 .JUMP]

def finish : List Located :=
  [opAt 2533 .JUMPDEST, pushAt 2534 2 1876, opAt 2535 .JUMP]

def fallback : List Located :=
  [opAt 2536 .JUMPDEST, opAt 2537 (.Dup ⟨0, by decide⟩),
   pushAt 2538 2 4096, pushAt 2539 2 1024, opAt 2540 .MCOPY,
   pushAt 2541 0 0, pushAt 2542 2 1769, opAt 2543 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3810 = true :=
  Artifact.isValidJumpDest_index 2474 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3849 = true :=
  Artifact.isValidJumpDest_index 2499 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3870 = true :=
  Artifact.isValidJumpDest_index 2511 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3871 = true :=
  Artifact.isValidJumpDest_index 2512 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3888 = true :=
  Artifact.isValidJumpDest_index 2519 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3915 = true :=
  Artifact.isValidJumpDest_index 2533 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3920 = true :=
  Artifact.isValidJumpDest_index 2536 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
