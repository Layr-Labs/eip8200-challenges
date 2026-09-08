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

@[simp] theorem directPC0 (i : Nat) (hi : 2421 ≤ i) (hii : i ≤ 2457) :
    Artifact.submissionArtifact.instructionPC i =
      [3806,3807,3808,3810,3811,3814,3815,3816,3818,3819,
       3820,3823,3824,3827,3828,3829,3830,3831,3833,3834,
       3835,3838,3839,3841,3844,3845,3846,3849,3850,3851,
       3853,3854,3858,3859,3860,3863,3864][i - 2421]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2458 ≤ i) (hii : i ≤ 2490) :
    Artifact.submissionArtifact.instructionPC i =
      [3866,3867,3868,3871,3874,3877,3880,3883,3884,3885,
       3887,3888,3889,3890,3893,3894,3895,3898,3901,3904,
       3907,3910,3911,3912,3915,3916,3917,3918,3921,3924,
       3925,3926,3929][i - 2458]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2421 .JUMPDEST, opAt 2422 (.Dup ⟨3, by decide⟩),
   pushAt 2423 1 3, opAt 2424 .EQ, pushAt 2425 2 3845,
   opAt 2426 .JUMPI]

def oneWidth : List Located :=
  [opAt 2427 (.Dup ⟨3, by decide⟩), pushAt 2428 1 1,
   opAt 2429 .EQ, opAt 2430 .ISZERO, pushAt 2431 2 3916,
   opAt 2432 .JUMPI]

def checkThree : List Located :=
  [pushAt 2433 2 9472, opAt 2434 .MLOAD, opAt 2435 .CALLDATALOAD,
   pushAt 2436 0 0, opAt 2437 .BYTE, pushAt 2438 1 3,
   opAt 2439 .EQ, opAt 2440 .ISZERO, pushAt 2441 2 3916,
   opAt 2442 .JUMPI]

def threeHit : List Located :=
  [pushAt 2443 1 1, pushAt 2444 2 3866, opAt 2445 .JUMP]

def check65537 : List Located :=
  [opAt 2446 .JUMPDEST, pushAt 2447 2 9472, opAt 2448 .MLOAD,
   opAt 2449 .CALLDATALOAD, pushAt 2450 1 232, opAt 2451 .SHR,
   pushAt 2452 3 65537, opAt 2453 .EQ, opAt 2454 .ISZERO,
   pushAt 2455 2 3916, opAt 2456 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2457 1 16]

def start : List Located :=
  [opAt 2458 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2459 .JUMPDEST, pushAt 2460 2 3884, pushAt 2461 2 2048,
   pushAt 2462 2 2048, pushAt 2463 2 2048, pushAt 2464 2 1939,
   opAt 2465 .JUMP]

def squareReturn : List Located :=
  [opAt 2466 .JUMPDEST, pushAt 2467 1 1,
   opAt 2468 (.Swap ⟨0, by decide⟩), opAt 2469 .SUB,
   opAt 2470 (.Dup ⟨0, by decide⟩), pushAt 2471 2 3867,
   opAt 2472 .JUMPI]

def product : List Located :=
  [opAt 2473 .POP, pushAt 2474 2 3911, pushAt 2475 2 1024,
   pushAt 2476 2 1024, pushAt 2477 2 2048, pushAt 2478 2 1939,
   opAt 2479 .JUMP]

def finish : List Located :=
  [opAt 2480 .JUMPDEST, pushAt 2481 2 1876, opAt 2482 .JUMP]

def fallback : List Located :=
  [opAt 2483 .JUMPDEST, opAt 2484 (.Dup ⟨0, by decide⟩),
   pushAt 2485 2 4096, pushAt 2486 2 1024, opAt 2487 .MCOPY,
   pushAt 2488 0 0, pushAt 2489 2 1769, opAt 2490 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3806 = true :=
  Artifact.isValidJumpDest_index 2421 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3845 = true :=
  Artifact.isValidJumpDest_index 2446 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3866 = true :=
  Artifact.isValidJumpDest_index 2458 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3867 = true :=
  Artifact.isValidJumpDest_index 2459 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3884 = true :=
  Artifact.isValidJumpDest_index 2466 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3911 = true :=
  Artifact.isValidJumpDest_index 2480 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3916 = true :=
  Artifact.isValidJumpDest_index 2483 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
