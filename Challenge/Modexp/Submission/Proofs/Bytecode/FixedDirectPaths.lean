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
    (hi : 2405 ≤ i) (hii : i ≤ 2441) :
    Artifact.submissionArtifact.instructionPC i =
      ([3887,3888,3889,3891,3892,3895,3896,3897,3899,3900,3901,3904,3905,3908,3909,3910,3911,3912,3914,3915,3916,3919,3920,3922,3925,3926,3927,3930,3931,3932,3934,3935,3939,3940,3941,3944,3945] : List Nat)[i - 2405]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2442 ≤ i) (hii : i ≤ 2474) :
    Artifact.submissionArtifact.instructionPC i =
      ([3947,3948,3949,3952,3955,3958,3961,3964,3965,3966,3968,3969,3970,3971,3974,3975,3976,3979,3982,3985,3988,3991,3992,3993,3996,3997,3998,3999,4002,4005,4006,4007,4010] : List Nat)[i - 2442]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2405 .JUMPDEST, opAt 2406 (.Dup ⟨3, by decide⟩),
   pushAt 2407 1 3, opAt 2408 .EQ, pushAt 2409 2 3926,
   opAt 2410 .JUMPI]

def oneWidth : List Located :=
  [opAt 2411 (.Dup ⟨3, by decide⟩), pushAt 2412 1 1,
   opAt 2413 .EQ, opAt 2414 .ISZERO, pushAt 2415 2 3997,
   opAt 2416 .JUMPI]

def checkThree : List Located :=
  [pushAt 2417 2 9472, opAt 2418 .MLOAD, opAt 2419 .CALLDATALOAD,
   pushAt 2420 0 0, opAt 2421 .BYTE, pushAt 2422 1 3,
   opAt 2423 .EQ, opAt 2424 .ISZERO, pushAt 2425 2 3997,
   opAt 2426 .JUMPI]

def threeHit : List Located :=
  [pushAt 2427 1 1, pushAt 2428 2 3947, opAt 2429 .JUMP]

def check65537 : List Located :=
  [opAt 2430 .JUMPDEST, pushAt 2431 2 9472, opAt 2432 .MLOAD,
   opAt 2433 .CALLDATALOAD, pushAt 2434 1 232, opAt 2435 .SHR,
   pushAt 2436 3 65537, opAt 2437 .EQ, opAt 2438 .ISZERO,
   pushAt 2439 2 3997, opAt 2440 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2441 1 16]

def start : List Located :=
  [opAt 2442 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2443 .JUMPDEST, pushAt 2444 2 3965, pushAt 2445 2 2048,
   pushAt 2446 2 2048, pushAt 2447 2 2048, pushAt 2448 2 1939,
   opAt 2449 .JUMP]

def squareReturn : List Located :=
  [opAt 2450 .JUMPDEST, pushAt 2451 1 1,
   opAt 2452 (.Swap ⟨0, by decide⟩), opAt 2453 .SUB,
   opAt 2454 (.Dup ⟨0, by decide⟩), pushAt 2455 2 3948,
   opAt 2456 .JUMPI]

def product : List Located :=
  [opAt 2457 .POP, pushAt 2458 2 3992, pushAt 2459 2 1024,
   pushAt 2460 2 1024, pushAt 2461 2 2048, pushAt 2462 2 1939,
   opAt 2463 .JUMP]

def finish : List Located :=
  [opAt 2464 .JUMPDEST, pushAt 2465 2 1876, opAt 2466 .JUMP]

def fallback : List Located :=
  [opAt 2467 .JUMPDEST, opAt 2468 (.Dup ⟨0, by decide⟩),
   pushAt 2469 2 4096, pushAt 2470 2 1024, opAt 2471 .MCOPY,
   pushAt 2472 0 0, pushAt 2473 2 1769, opAt 2474 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3887 = true :=
  Artifact.isValidJumpDest_index 2405 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3926 = true :=
  Artifact.isValidJumpDest_index 2430 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3947 = true :=
  Artifact.isValidJumpDest_index 2442 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3948 = true :=
  Artifact.isValidJumpDest_index 2443 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3965 = true :=
  Artifact.isValidJumpDest_index 2450 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3992 = true :=
  Artifact.isValidJumpDest_index 2464 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3997 = true :=
  Artifact.isValidJumpDest_index 2467 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
