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

@[simp] theorem directPC0 (i : Nat)
    (hi : 2414 ≤ i) (hii : i ≤ 2450) :
    Artifact.submissionArtifact.instructionPC i =
      ([3887,3888,3889,3891,3892,3895,3896,3897,3899,3900,3901,3904,3905,3908,3909,3910,3911,3912,3914,3915,3916,3919,3920,3922,3925,3926,3927,3930,3931,3932,3934,3935,3939,3940,3941,3944,3945] : List Nat)[i - 2414]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2451 ≤ i) (hii : i ≤ 2483) :
    Artifact.submissionArtifact.instructionPC i =
      ([3947,3948,3949,3952,3955,3958,3961,3964,3965,3966,3968,3969,3970,3971,3974,3975,3976,3979,3982,3985,3988,3991,3992,3993,3996,3997,3998,3999,4002,4005,4006,4007,4010] : List Nat)[i - 2451]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2414 .JUMPDEST, opAt 2415 (.Dup ⟨3, by decide⟩),
   pushAt 2416 1 3, opAt 2417 .EQ, pushAt 2418 2 3926,
   opAt 2419 .JUMPI]

def oneWidth : List Located :=
  [opAt 2420 (.Dup ⟨3, by decide⟩), pushAt 2421 1 1,
   opAt 2422 .EQ, opAt 2423 .ISZERO, pushAt 2424 2 3997,
   opAt 2425 .JUMPI]

def checkThree : List Located :=
  [pushAt 2426 2 9472, opAt 2427 .MLOAD, opAt 2428 .CALLDATALOAD,
   pushAt 2429 0 0, opAt 2430 .BYTE, pushAt 2431 1 3,
   opAt 2432 .EQ, opAt 2433 .ISZERO, pushAt 2434 2 3997,
   opAt 2435 .JUMPI]

def threeHit : List Located :=
  [pushAt 2436 1 1, pushAt 2437 2 3947, opAt 2438 .JUMP]

def check65537 : List Located :=
  [opAt 2439 .JUMPDEST, pushAt 2440 2 9472, opAt 2441 .MLOAD,
   opAt 2442 .CALLDATALOAD, pushAt 2443 1 232, opAt 2444 .SHR,
   pushAt 2445 3 65537, opAt 2446 .EQ, opAt 2447 .ISZERO,
   pushAt 2448 2 3997, opAt 2449 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2450 1 16]

def start : List Located :=
  [opAt 2451 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2452 .JUMPDEST, pushAt 2453 2 3965, pushAt 2454 2 2048,
   pushAt 2455 2 2048, pushAt 2456 2 2048, pushAt 2457 2 1939,
   opAt 2458 .JUMP]

def squareReturn : List Located :=
  [opAt 2459 .JUMPDEST, pushAt 2460 1 1,
   opAt 2461 (.Swap ⟨0, by decide⟩), opAt 2462 .SUB,
   opAt 2463 (.Dup ⟨0, by decide⟩), pushAt 2464 2 3948,
   opAt 2465 .JUMPI]

def product : List Located :=
  [opAt 2466 .POP, pushAt 2467 2 3992, pushAt 2468 2 1024,
   pushAt 2469 2 1024, pushAt 2470 2 2048, pushAt 2471 2 1939,
   opAt 2472 .JUMP]

def finish : List Located :=
  [opAt 2473 .JUMPDEST, pushAt 2474 2 1876, opAt 2475 .JUMP]

def fallback : List Located :=
  [opAt 2476 .JUMPDEST, opAt 2477 (.Dup ⟨0, by decide⟩),
   pushAt 2478 2 4096, pushAt 2479 2 1024, opAt 2480 .MCOPY,
   pushAt 2481 0 0, pushAt 2482 2 1769, opAt 2483 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3887 = true :=
  Artifact.isValidJumpDest_index 2414 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3926 = true :=
  Artifact.isValidJumpDest_index 2439 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3947 = true :=
  Artifact.isValidJumpDest_index 2451 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3948 = true :=
  Artifact.isValidJumpDest_index 2452 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3965 = true :=
  Artifact.isValidJumpDest_index 2459 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3992 = true :=
  Artifact.isValidJumpDest_index 2473 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3997 = true :=
  Artifact.isValidJumpDest_index 2476 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
