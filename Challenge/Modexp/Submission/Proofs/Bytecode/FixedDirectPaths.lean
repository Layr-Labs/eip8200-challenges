import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3241 (`0x0c6b`).  Each in-place square enters
the kernel's shared `common` block with `hd = sq_row`; the final
mixed-domain product enters the kernel's multiply entry.  For the accelerated
widths the kernel loops internally and returns to `after_sq` (pc 3304), so the
loop head first stores the square count in memory word `0x2440 = 9280`.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2013 ≤ i) (hii : i ≤ 2046) :
    Artifact.submissionArtifact.instructionPC i =
      ([2441,2442,2443,2445,2446,2449,2450,2451,2453,2454,2457,2458,2461,2462,2463,2464,2465,2467,2468,2471,2472,2474,2477,2478,2479,2482,2483,2484,2486,2487,2491,2492,2495,2496] : List Nat)[i - 2013]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 2047 ≤ i) (hii : i ≤ 2071) :
    Artifact.submissionArtifact.instructionPC i =
      ([2498,2499,2500,2503,2504,2507,2510,2511,2512,2515,2518,2519,2520,2521,2522,2523,2524,2527,2528,2529,2532,2535,2536,2539,2542] : List Nat)[i - 2047]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2036 .JUMPDEST,
   pushAt 2037 2 2816,
   opAt 2038 .MLOAD,
   opAt 2039 .CALLDATALOAD,
   pushAt 2040 1 232,
   opAt 2041 .SHR,
   pushAt 2042 3 65537,
   opAt 2043 .XOR,
   pushAt 2044 2 790,
   opAt 2045 .JUMPI]

def checkThree : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2024 2 2816,
   opAt 2025 .MLOAD,
   opAt 2026 .CALLDATALOAD,
   pushAt 2027 0 0,
   opAt 2028 .BYTE,
   pushAt 2029 1 3,
   opAt 2030 .XOR,
   pushAt 2031 2 790,
   opAt 2032 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2013 .JUMPDEST,
   opAt 2014 (.Dup ⟨3, by decide⟩),
   pushAt 2015 1 3,
   opAt 2016 .EQ,
   pushAt 2017 2 2478,
   opAt 2018 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2046 1 16]

def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2019 (.Dup ⟨3, by decide⟩),
   pushAt 2020 1 1,
   opAt 2021 .XOR,
   pushAt 2022 2 790,
   opAt 2023 .JUMPI]

def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2033 1 1,
   pushAt 2034 2 2498,
   opAt 2035 .JUMP]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3292. -/
def squareCall : List Located :=
  [opAt 2047 .JUMPDEST,
   opAt 2048 (.Dup ⟨0, by decide⟩),
   pushAt 2049 2 2624,
   opAt 2050 .MSTORE,
   pushAt 2051 2 2519,
   pushAt 2052 2 512,
   opAt 2053 (.Dup ⟨0, by decide⟩),
   opAt 2054 (.Dup ⟨0, by decide⟩),
   pushAt 2055 2 4561,
   pushAt 2056 2 3394,
   opAt 2057 .JUMP]

def squareReturn : List Located :=
  [opAt 2058 .JUMPDEST,
   pushAt 2059 0 0,
   opAt 2060 .NOT,
   opAt 2061 .ADD,
   opAt 2062 (.Dup ⟨0, by decide⟩),
   pushAt 2063 2 2498,
   opAt 2064 .JUMPI]

/-- `after_sq` (pc 3304): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2065 .POP,
   pushAt 2066 2 774,
   pushAt 2067 2 256,
   opAt 2068 (.Dup ⟨0, by decide⟩),
   pushAt 2069 2 512,
   pushAt 2070 2 3390,
   opAt 2071 .JUMP]


theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2441 = true :=
  Artifact.isValidJumpDest_index 2013 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2478 = true :=
  Artifact.isValidJumpDest_index 2036 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2498 = true :=
  Artifact.isValidJumpDest_index 2047 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2519 = true :=
  Artifact.isValidJumpDest_index 2058 (by rfl)

/-- `BAIL6` (pc 1054), the target of all three recogniser misses. -/
theorem jumpDestBail :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 790 = true :=
  Artifact.isValidJumpDest_index 568 (by rfl)

/-- `modexpBig` (pc 237), where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 238 = true :=
  Artifact.isValidJumpDest_index 165 (by rfl)

theorem pcTramp717 : Artifact.submissionArtifact.instructionPC 568 = 790 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem pcTramp718 : Artifact.submissionArtifact.instructionPC 569 = 791 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem pcTramp719 : Artifact.submissionArtifact.instructionPC 570 = 793 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- The six-word bail trampoline: `JUMPDEST; PUSH1 237; JUMP`. -/
def bail : List Located :=
  [opAt 568 .JUMPDEST,
   pushAt 569 1 238,
   opAt 570 .JUMP]

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3390 = true :=
  Artifact.isValidJumpDest_index 2713 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3394 = true :=
  Artifact.isValidJumpDest_index 2715 (by rfl)


/- `after_sq` (pc 3304): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
