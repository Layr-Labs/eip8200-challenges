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

@[simp] theorem fixedPC0 (i : Nat) (hi : 2342 ≤ i) (hii : i ≤ 2378) :
    Artifact.submissionArtifact.instructionPC i =
      [3695,3696,3698,3699,3700,3701,3703,3704,3706,3707,3708,3709,3710,
       3712,3713,3714,3715,3716,3717,3718,3719,3720,3721,3723,
       3724,3726,3727,3728,3729,3730,3732,3733,3734,3735,3736,
       3737,3738][i - 2342]! := by
  interval_cases i <;> decide

@[simp] theorem fixedPC1 (i : Nat) (hi : 2379 ≤ i) (hii : i ≤ 2427) :
    Artifact.submissionArtifact.instructionPC i =
      [3739,3740,3741,3743,3744,3746,3747,3748,3749,3750,3752,3753,3754,
       3755,3756,3757,3758,3759,3760,3761,3763,3764,3766,3767,
       3768,3769,3770,3772,3773,3774,3775,3776,3777,3778,3779,
       3780,3781,3783,3784,3786,3787,3788,3789,3790,3792,3793,
       3794,3795,3796][i - 2379]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2342 .JUMPDEST, opAt 2343 (.Dup ⟨3, by decide⟩),
   pushAt 2344 1 3, opAt 2345 .EQ, pushAt 2346 2 3734,
   opAt 2347 .JUMPI]

def oneWidth : List Located :=
  [opAt 2348 (.Dup ⟨3, by decide⟩), pushAt 2349 1 1,
   opAt 2350 .EQ, opAt 2351 .ISZERO, pushAt 2352 2 3838,
   opAt 2353 .JUMPI]

def checkThree : List Located :=
  [pushAt 2354 2 9472, opAt 2355 .MLOAD, opAt 2356 .CALLDATALOAD,
   pushAt 2357 0 0, opAt 2358 .BYTE, pushAt 2359 1 3,
   opAt 2360 .EQ, opAt 2361 .ISZERO, pushAt 2362 2 3838,
   opAt 2363 .JUMPI]

def threeHit : List Located :=
  [pushAt 2364 1 1, pushAt 2365 2 3755, opAt 2366 .JUMP]

def check65537 : List Located :=
  [opAt 2367 .JUMPDEST, pushAt 2368 2 9472, opAt 2369 .MLOAD,
   opAt 2370 .CALLDATALOAD, pushAt 2371 1 232, opAt 2372 .SHR,
   pushAt 2373 3 65537, opAt 2374 .EQ, opAt 2375 .ISZERO,
   pushAt 2376 2 3838, opAt 2377 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2378 1 16]

def start : List Located :=
  [opAt 2379 .JUMPDEST, opAt 2380 (.Dup ⟨1, by decide⟩),
   pushAt 2381 2 2048, pushAt 2382 2 1024, opAt 2383 .MCOPY]

def squareCall : List Located :=
  [opAt 2384 .JUMPDEST, pushAt 2385 2 3781, pushAt 2386 2 1024,
   pushAt 2387 2 1024, pushAt 2388 2 1024, pushAt 2389 2 1939,
   opAt 2390 .JUMP]

def squareReturn : List Located :=
  [opAt 2391 .JUMPDEST, pushAt 2392 1 1, opAt 2393 (.Swap ⟨0, by decide⟩),
   opAt 2394 .SUB, opAt 2395 (.Dup ⟨0, by decide⟩),
   pushAt 2396 2 3764, opAt 2397 .JUMPI]

def product : List Located :=
  [opAt 2398 .POP, pushAt 2399 2 3808, pushAt 2400 2 1024,
   pushAt 2401 2 2048, pushAt 2402 2 1024, pushAt 2403 2 1939,
   opAt 2404 .JUMP]

def decode : List Located :=
  [opAt 2405 .JUMPDEST, pushAt 2406 1 1,
   opAt 2407 (.Dup ⟨1, by decide⟩), pushAt 2408 2 3040,
   opAt 2409 .ADD, opAt 2410 .MSTORE, pushAt 2411 2 3833,
   pushAt 2412 2 1024, pushAt 2413 2 3072, pushAt 2414 2 1024,
   pushAt 2415 2 1939, opAt 2416 .JUMP]

def finish : List Located :=
  [opAt 2417 .JUMPDEST, pushAt 2418 2 1876, opAt 2419 .JUMP]

def fallback : List Located :=
  [opAt 2420 .JUMPDEST, opAt 2421 (.Dup ⟨0, by decide⟩),
   pushAt 2422 2 4096, pushAt 2423 2 1024, opAt 2424 .MCOPY,
   pushAt 2425 0 0, pushAt 2426 2 1769, opAt 2427 .JUMP]

theorem jumpDest3695 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3695 = true :=
  Artifact.isValidJumpDest_index 2342 (by rfl)

theorem jumpDest3734 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3734 = true :=
  Artifact.isValidJumpDest_index 2367 (by rfl)

theorem jumpDest3755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3755 = true :=
  Artifact.isValidJumpDest_index 2379 (by rfl)

theorem jumpDest3764 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3764 = true :=
  Artifact.isValidJumpDest_index 2384 (by rfl)

theorem jumpDest3781 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3781 = true :=
  Artifact.isValidJumpDest_index 2391 (by rfl)

theorem jumpDest3808 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3808 = true :=
  Artifact.isValidJumpDest_index 2405 (by rfl)

theorem jumpDest3833 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3833 = true :=
  Artifact.isValidJumpDest_index 2417 (by rfl)

theorem jumpDest3838 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3838 = true :=
  Artifact.isValidJumpDest_index 2420 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths
