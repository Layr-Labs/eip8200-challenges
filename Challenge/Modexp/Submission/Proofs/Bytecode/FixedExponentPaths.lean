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

@[simp] theorem fixedPC0 (i : Nat) (hi : 2414 ≤ i) (hii : i ≤ 2450) :
    Artifact.submissionArtifact.instructionPC i =
      [3695,3696,3697,3699,3700,3703,3704,3705,3707,3708,
       3709,3712,3713,3716,3717,3718,3719,3720,3722,3723,
       3724,3727,3728,3730,3733,3734,3735,3738,3739,3740,
       3742,3743,3747,3748,3749,3752,3753][i - 2414]! := by
  interval_cases i <;> decide

@[simp] theorem fixedPC1 (i : Nat) (hi : 2451 ≤ i) (hii : i ≤ 2499) :
    Artifact.submissionArtifact.instructionPC i =
      [3755,3756,3757,3760,3763,3764,3765,3768,3771,3774,
       3777,3780,3781,3782,3784,3785,3786,3787,3790,3791,
       3792,3795,3798,3801,3804,3807,3808,3809,3811,3812,
       3815,3816,3817,3820,3823,3826,3829,3832,3833,3834,
       3837,3838,3839,3840,3843,3846,3847,3848,3851][i - 2451]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2310 .JUMPDEST, opAt 2311 (.Dup ⟨3, by decide⟩),
   pushAt 2312 1 3, opAt 2313 .EQ, pushAt 2314 2 3734,
   opAt 2315 .JUMPI]

def oneWidth : List Located :=
  [opAt 2316 (.Dup ⟨3, by decide⟩), pushAt 2317 1 1,
   opAt 2318 .EQ, opAt 2319 .ISZERO, pushAt 2320 2 3838,
   opAt 2321 .JUMPI]

def checkThree : List Located :=
  [pushAt 2322 2 9472, opAt 2323 .MLOAD, opAt 2324 .CALLDATALOAD,
   pushAt 2325 0 0, opAt 2326 .BYTE, pushAt 2327 1 3,
   opAt 2328 .EQ, opAt 2329 .ISZERO, pushAt 2330 2 3838,
   opAt 2331 .JUMPI]

def threeHit : List Located :=
  [pushAt 2332 1 1, pushAt 2333 2 3755, opAt 2334 .JUMP]

def check65537 : List Located :=
  [opAt 2335 .JUMPDEST, pushAt 2336 2 9472, opAt 2337 .MLOAD,
   opAt 2338 .CALLDATALOAD, pushAt 2339 1 232, opAt 2340 .SHR,
   pushAt 2341 3 65537, opAt 2342 .EQ, opAt 2343 .ISZERO,
   pushAt 2344 2 3838, opAt 2345 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2346 1 16]

def start : List Located :=
  [opAt 2347 .JUMPDEST, opAt 2348 (.Dup ⟨1, by decide⟩),
   pushAt 2349 2 2048, pushAt 2350 2 1024, opAt 2351 .MCOPY]

def squareCall : List Located :=
  [opAt 2352 .JUMPDEST, pushAt 2353 2 3781, pushAt 2354 2 1024,
   pushAt 2355 2 1024, pushAt 2356 2 1024, pushAt 2357 2 1939,
   opAt 2358 .JUMP]

def squareReturn : List Located :=
  [opAt 2359 .JUMPDEST, pushAt 2360 1 1, opAt 2361 (.Swap ⟨0, by decide⟩),
   opAt 2362 .SUB, opAt 2363 (.Dup ⟨0, by decide⟩),
   pushAt 2364 2 3764, opAt 2365 .JUMPI]

def product : List Located :=
  [opAt 2366 .POP, pushAt 2367 2 3808, pushAt 2368 2 1024,
   pushAt 2369 2 2048, pushAt 2370 2 1024, pushAt 2371 2 1939,
   opAt 2372 .JUMP]

def decode : List Located :=
  [opAt 2373 .JUMPDEST, pushAt 2374 1 1,
   opAt 2375 (.Dup ⟨1, by decide⟩), pushAt 2376 2 3040,
   opAt 2377 .ADD, opAt 2378 .MSTORE, pushAt 2379 2 3833,
   pushAt 2380 2 1024, pushAt 2381 2 3072, pushAt 2382 2 1024,
   pushAt 2383 2 1939, opAt 2384 .JUMP]

def finish : List Located :=
  [opAt 2385 .JUMPDEST, pushAt 2386 2 1876, opAt 2387 .JUMP]

def fallback : List Located :=
  [opAt 2388 .JUMPDEST, opAt 2389 (.Dup ⟨0, by decide⟩),
   pushAt 2390 2 4096, pushAt 2391 2 1024, opAt 2392 .MCOPY,
   pushAt 2393 0 0, pushAt 2394 2 1769, opAt 2395 .JUMP]

theorem jumpDest3695 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3695 = true :=
  Artifact.isValidJumpDest_index 2310 (by rfl)

theorem jumpDest3734 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3734 = true :=
  Artifact.isValidJumpDest_index 2335 (by rfl)

theorem jumpDest3755 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3755 = true :=
  Artifact.isValidJumpDest_index 2347 (by rfl)

theorem jumpDest3764 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3764 = true :=
  Artifact.isValidJumpDest_index 2352 (by rfl)

theorem jumpDest3781 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3781 = true :=
  Artifact.isValidJumpDest_index 2359 (by rfl)

theorem jumpDest3808 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3808 = true :=
  Artifact.isValidJumpDest_index 2373 (by rfl)

theorem jumpDest3833 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3833 = true :=
  Artifact.isValidJumpDest_index 2385 (by rfl)

theorem jumpDest3838 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3838 = true :=
  Artifact.isValidJumpDest_index 2388 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentPaths
