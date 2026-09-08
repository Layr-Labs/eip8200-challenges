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
    (hi : 2390 ≤ i) (hii : i ≤ 2426) :
    Artifact.submissionArtifact.instructionPC i =
      [3854,3855,3856,3858,3859,3862,3863,3864,3866,3867,3868,3871,3872,3875,3876,3877,3878,3879,3881,3882,3883,3886,3887,3889,3892,3893,3894,3897,3898,3899,3901,3902,3906,3907,3908,3911,3912][i - 2390]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2427 ≤ i) (hii : i ≤ 2459) :
    Artifact.submissionArtifact.instructionPC i =
      [3914,3915,3916,3919,3922,3925,3928,3931,3932,3933,3935,3936,3937,3938,3941,3942,3943,3946,3949,3952,3955,3958,3959,3960,3963,3964,3965,3966,3969,3972,3973,3974,3977][i - 2427]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2390 .JUMPDEST, opAt 2391 (.Dup ⟨3, by decide⟩),
   pushAt 2392 1 3, opAt 2393 .EQ, pushAt 2394 2 3893,
   opAt 2395 .JUMPI]

def oneWidth : List Located :=
  [opAt 2396 (.Dup ⟨3, by decide⟩), pushAt 2397 1 1,
   opAt 2398 .EQ, opAt 2399 .ISZERO, pushAt 2400 2 3964,
   opAt 2401 .JUMPI]

def checkThree : List Located :=
  [pushAt 2402 2 9472, opAt 2403 .MLOAD, opAt 2404 .CALLDATALOAD,
   pushAt 2405 0 0, opAt 2406 .BYTE, pushAt 2407 1 3,
   opAt 2408 .EQ, opAt 2409 .ISZERO, pushAt 2410 2 3964,
   opAt 2411 .JUMPI]

def threeHit : List Located :=
  [pushAt 2412 1 1, pushAt 2413 2 3914, opAt 2414 .JUMP]

def check65537 : List Located :=
  [opAt 2415 .JUMPDEST, pushAt 2416 2 9472, opAt 2417 .MLOAD,
   opAt 2418 .CALLDATALOAD, pushAt 2419 1 232, opAt 2420 .SHR,
   pushAt 2421 3 65537, opAt 2422 .EQ, opAt 2423 .ISZERO,
   pushAt 2424 2 3964, opAt 2425 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2426 1 16]

def start : List Located :=
  [opAt 2427 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2428 .JUMPDEST, pushAt 2429 2 3932, pushAt 2430 2 2048,
   pushAt 2431 2 2048, pushAt 2432 2 2048, pushAt 2433 2 4751,
   opAt 2434 .JUMP]

def squareReturn : List Located :=
  [opAt 2435 .JUMPDEST, pushAt 2436 1 1,
   opAt 2437 (.Swap ⟨0, by decide⟩), opAt 2438 .SUB,
   opAt 2439 (.Dup ⟨0, by decide⟩), pushAt 2440 2 3915,
   opAt 2441 .JUMPI]

def product : List Located :=
  [opAt 2442 .POP, pushAt 2443 2 3959, pushAt 2444 2 1024,
   pushAt 2445 2 1024, pushAt 2446 2 2048, pushAt 2447 2 4751,
   opAt 2448 .JUMP]

def finish : List Located :=
  [opAt 2449 .JUMPDEST, pushAt 2450 2 1852, opAt 2451 .JUMP]

def fallback : List Located :=
  [opAt 2452 .JUMPDEST, opAt 2453 (.Dup ⟨0, by decide⟩),
   pushAt 2454 2 4096, pushAt 2455 2 1024, opAt 2456 .MCOPY,
   pushAt 2457 0 0, pushAt 2458 2 1746, opAt 2459 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3854 = true :=
  Artifact.isValidJumpDest_index 2390 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3893 = true :=
  Artifact.isValidJumpDest_index 2415 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3914 = true :=
  Artifact.isValidJumpDest_index 2427 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3915 = true :=
  Artifact.isValidJumpDest_index 2428 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3932 = true :=
  Artifact.isValidJumpDest_index 2435 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3959 = true :=
  Artifact.isValidJumpDest_index 2449 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3964 = true :=
  Artifact.isValidJumpDest_index 2452 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
