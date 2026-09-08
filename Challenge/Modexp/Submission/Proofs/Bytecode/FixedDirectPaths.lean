import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The appended handler occupies pc3892..3523 and instruction indices2572..2308.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat)
    (hi : 2413 ≤ i) (hii : i ≤ 2449) :
    Artifact.submissionArtifact.instructionPC i =
      [3374,3375,3376,3378,3379,3382,3383,3384,3386,3387,3388,3391,3392,3395,3396,3397,3398,3399,3401,3402,3403,3406,3407,3409,3412,3413,3414,3417,3418,3419,3421,3422,3426,3427,3428,3431,3432][i - 2413]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2450 ≤ i) (hii : i ≤ 2482) :
    Artifact.submissionArtifact.instructionPC i =
      [3434,3435,3436,3439,3442,3445,3448,3451,3452,3453,3455,3456,3457,3458,3461,3462,3463,3466,3469,3472,3475,3478,3479,3480,3483,3484,3485,3486,3489,3492,3493,3494,3497][i - 2450]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2413 .JUMPDEST, opAt 2414 (.Dup ⟨3, by decide⟩),
   pushAt 2415 1 3, opAt 2416 .EQ, pushAt 2417 2 3413,
   opAt 2418 .JUMPI]

def oneWidth : List Located :=
  [opAt 2419 (.Dup ⟨3, by decide⟩), pushAt 2420 1 1,
   opAt 2421 .EQ, opAt 2422 .ISZERO, pushAt 2423 2 3484,
   opAt 2424 .JUMPI]

def checkThree : List Located :=
  [pushAt 2425 2 9472, opAt 2426 .MLOAD, opAt 2427 .CALLDATALOAD,
   pushAt 2428 0 0, opAt 2429 .BYTE, pushAt 2430 1 3,
   opAt 2431 .EQ, opAt 2432 .ISZERO, pushAt 2433 2 3484,
   opAt 2434 .JUMPI]

def threeHit : List Located :=
  [pushAt 2435 1 1, pushAt 2436 2 3434, opAt 2437 .JUMP]

def check65537 : List Located :=
  [opAt 2438 .JUMPDEST, pushAt 2439 2 9472, opAt 2440 .MLOAD,
   opAt 2441 .CALLDATALOAD, pushAt 2442 1 232, opAt 2443 .SHR,
   pushAt 2444 3 65537, opAt 2445 .EQ, opAt 2446 .ISZERO,
   pushAt 2447 2 3484, opAt 2448 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2449 1 16]

def start : List Located :=
  [opAt 2450 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2451 .JUMPDEST, pushAt 2452 2 3452, pushAt 2453 2 2048,
   pushAt 2454 2 2048, pushAt 2455 2 2048, pushAt 2456 2 4176,
   opAt 2457 .JUMP]

def squareReturn : List Located :=
  [opAt 2458 .JUMPDEST, pushAt 2459 1 1,
   opAt 2460 (.Swap ⟨0, by decide⟩), opAt 2461 .SUB,
   opAt 2462 (.Dup ⟨0, by decide⟩), pushAt 2463 2 3435,
   opAt 2464 .JUMPI]

def product : List Located :=
  [opAt 2465 .POP, pushAt 2466 2 3479, pushAt 2467 2 1024,
   pushAt 2468 2 1024, pushAt 2469 2 2048, pushAt 2470 2 4176,
   opAt 2471 .JUMP]

def finish : List Located :=
  [opAt 2472 .JUMPDEST, pushAt 2473 2 1867, opAt 2474 .JUMP]

def fallback : List Located :=
  [opAt 2475 .JUMPDEST, opAt 2476 (.Dup ⟨0, by decide⟩),
   pushAt 2477 2 4096, pushAt 2478 2 1024, opAt 2479 .MCOPY,
   pushAt 2480 0 0, pushAt 2481 2 1761, opAt 2482 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3374 = true :=
  Artifact.isValidJumpDest_index 2413 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3413 = true :=
  Artifact.isValidJumpDest_index 2438 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3434 = true :=
  Artifact.isValidJumpDest_index 2450 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3435 = true :=
  Artifact.isValidJumpDest_index 2451 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3452 = true :=
  Artifact.isValidJumpDest_index 2458 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3479 = true :=
  Artifact.isValidJumpDest_index 2472 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3484 = true :=
  Artifact.isValidJumpDest_index 2475 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
