import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3179 (`0x0c6b`).  Each in-place square enters
the kernel's shared `common` block with `hd = sq_row`; the final
mixed-domain product enters the kernel's multiply entry.  For the accelerated
widths the kernel loops internally and returns to `after_sq` (pc 3243), so the
loop head first stores the square count in memory word `0x2440 = 9280`.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2326 ≤ i) (hii : i ≤ 2362) :
    Artifact.submissionArtifact.instructionPC i =
      ([3005,3006,3007,3010,3011,3012,3014,3015,3018,3019,3020,3022,3023,3026,3027,3030,3031,3032,3033,3034,3036,3037,3040,3041,3043,3046,3047,3048,3051,3052,3053,3055,3056,3060,3061,3064,3065] : List Nat)[i - 2326]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2363 ≤ i) (hii : i ≤ 2396) :
    Artifact.submissionArtifact.instructionPC i =
      ([3067,3068,3069,3072,3073,3076,3079,3080,3081,3084,3087,3088,3089,3091,3092,3093,3094,3097,3098,3099,3100,3103,3106,3107,3110,3113,3114,3115,3116,3119,3122,3123,3124,3127] : List Nat)[i - 2363]! := by
  interval_cases i <;> decide


-- At index 2433 the pushed target 3144 IS the fall-through pc, and the `JUMPDEST` at
-- 3144 is the next element of this very list, so `POP` lands where `JUMP` did with an
-- identical stack and pc.  Keep this note OUTSIDE the list: a comment between entries is
-- legal Lean, but a line-oriented reader of this list sees the entry as missing.
def entryPrefix : List Located :=
  [opAt 2326 .JUMPDEST,
   opAt 2327 (.Dup ⟨3, by decide⟩),
   pushAt 2328 2 3011,
   opAt 2329 .POP,
   opAt 2330 .JUMPDEST,
   pushAt 2331 1 3,
   opAt 2332 .EQ,
   pushAt 2333 2 3047,
   opAt 2334 .JUMPI]

def oneWidth : List Located :=
  [opAt 2335 (.Dup ⟨3, by decide⟩),
   pushAt 2336 1 1,
   opAt 2337 .XOR,
   pushAt 2338 2 3114,
   opAt 2339 .JUMPI]

def checkThree : List Located :=
  [pushAt 2340 2 9472,
   opAt 2341 .MLOAD,
   opAt 2342 .CALLDATALOAD,
   pushAt 2343 0 0,
   opAt 2344 .BYTE,
   pushAt 2345 1 3,
   opAt 2346 .XOR,
   pushAt 2347 2 3114,
   opAt 2348 .JUMPI]

def threeHit : List Located :=
  [pushAt 2349 1 1,
   pushAt 2350 2 3067,
   opAt 2351 .JUMP]

def check65537 : List Located :=
  [opAt 2352 .JUMPDEST,
   pushAt 2353 2 9472,
   opAt 2354 .MLOAD,
   opAt 2355 .CALLDATALOAD,
   pushAt 2356 1 232,
   opAt 2357 .SHR,
   pushAt 2358 3 65537,
   opAt 2359 .XOR,
   pushAt 2360 2 3114,
   opAt 2361 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2362 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3233. -/
def squareCall : List Located :=
  [opAt 2363 .JUMPDEST,
   opAt 2364 (.Dup ⟨0, by decide⟩),
   pushAt 2365 2 9280,
   opAt 2366 .MSTORE,
   pushAt 2367 2 3088,
   pushAt 2368 2 2048,
   opAt 2369 (.Dup ⟨0, by decide⟩),
   opAt 2370 (.Dup ⟨0, by decide⟩),
   pushAt 2371 2 4699,
   pushAt 2372 2 3783,
   opAt 2373 .JUMP]

def squareReturn : List Located :=
  [opAt 2374 .JUMPDEST,
   pushAt 2375 1 1,
   opAt 2376 (.Swap ⟨0, by decide⟩),
   opAt 2377 .SUB,
   opAt 2378 (.Dup ⟨0, by decide⟩),
   pushAt 2379 2 3067,
   opAt 2380 .JUMPI]

/-- `after_sq` (pc 3243): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2381 .JUMPDEST,
   opAt 2382 .POP,
   pushAt 2383 2 1438,
   pushAt 2384 2 1024,
   opAt 2385 (.Dup ⟨0, by decide⟩),
   pushAt 2386 2 2048,
   pushAt 2387 2 3779,
   opAt 2388 .JUMP]

def fallback : List Located :=
  [opAt 2389 .JUMPDEST,
   opAt 2390 (.Dup ⟨0, by decide⟩),
   pushAt 2391 2 4096,
   pushAt 2392 2 1024,
   opAt 2393 .MCOPY,
   pushAt 2394 0 0,
   pushAt 2395 2 1341,
   opAt 2396 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3005 = true :=
  Artifact.isValidJumpDest_index 2326 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3047 = true :=
  Artifact.isValidJumpDest_index 2352 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3067 = true :=
  Artifact.isValidJumpDest_index 2363 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3088 = true :=
  Artifact.isValidJumpDest_index 2374 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3114 = true :=
  Artifact.isValidJumpDest_index 2389 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3779 = true :=
  Artifact.isValidJumpDest_index 2849 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3783 = true :=
  Artifact.isValidJumpDest_index 2851 (by rfl)

/-- Target of the (now contiguous) jump from `0x0c6d` to `0x0c71`. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3011 = true :=
  Artifact.isValidJumpDest_index 2330 (by rfl)

/-- `after_sq` (pc 3243): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3098 = true :=
  Artifact.isValidJumpDest_index 2381 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
