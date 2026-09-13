import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc 3240 (`0x0c6b`).  Each in-place square enters
the kernel's shared `common` block with `hd = sq_row`; the final
mixed-domain product enters the kernel's multiply entry.  For the accelerated
widths the kernel loops internally and returns to `after_sq` (pc 3303), so the
loop head first stores the square count in memory word `0x2440 = 9280`.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 1992 ≤ i) (hii : i ≤ 2025) :
    Artifact.submissionArtifact.instructionPC i =
      ([2637,2638,2639,2641,2642,2645,2646,2647,2649,2650,2653,2654,2657,2658,2659,2660,2661,2663,2664,2667,2668,2670,2673,2674,2675,2678,2679,2680,2682,2683,2687,2688,2691,2692] : List Nat)[i - 1992]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 2026 ≤ i) (hii : i ≤ 2058) :
    Artifact.submissionArtifact.instructionPC i =
      ([2694,2695,2696,2699,2700,2703,2706,2707,2708,2711,2714,2715,2716,2717,2718,2719,2720,2723,2724,2725,2728,2731,2732,2735,2738,2739,2740,2741,2744,2747,2748,2749,2752] : List Nat)[i - 2026]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2015 .JUMPDEST,
   pushAt 2016 2 2816,
   opAt 2017 .MLOAD,
   opAt 2018 .CALLDATALOAD,
   pushAt 2019 1 232,
   opAt 2020 .SHR,
   pushAt 2021 3 65537,
   opAt 2022 .XOR,
   pushAt 2023 2 2739,
   opAt 2024 .JUMPI]

def checkThree : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2003 2 2816,
   opAt 2004 .MLOAD,
   opAt 2005 .CALLDATALOAD,
   pushAt 2006 0 0,
   opAt 2007 .BYTE,
   pushAt 2008 1 3,
   opAt 2009 .XOR,
   pushAt 2010 2 2739,
   opAt 2011 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1992 .JUMPDEST,
   opAt 1993 (.Dup ⟨3, by decide⟩),
   pushAt 1994 1 3,
   opAt 1995 .EQ,
   pushAt 1996 2 2674,
   opAt 1997 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2025 1 16]

def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1998 (.Dup ⟨3, by decide⟩),
   pushAt 1999 1 1,
   opAt 2000 .XOR,
   pushAt 2001 2 2739,
   opAt 2002 .JUMPI]

def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2012 1 1,
   pushAt 2013 2 2694,
   opAt 2014 .JUMP]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3294. -/
def squareCall : List Located :=
  [opAt 2026 .JUMPDEST,
   opAt 2027 (.Dup ⟨0, by decide⟩),
   pushAt 2028 2 2624,
   opAt 2029 .MSTORE,
   pushAt 2030 2 2715,
   pushAt 2031 2 512,
   opAt 2032 (.Dup ⟨0, by decide⟩),
   opAt 2033 (.Dup ⟨0, by decide⟩),
   pushAt 2034 2 4754,
   pushAt 2035 2 3551,
   opAt 2036 .JUMP]

def squareReturn : List Located :=
  [opAt 2037 .JUMPDEST,
   pushAt 2038 0 0,
   opAt 2039 .NOT,
   opAt 2040 .ADD,
   opAt 2041 (.Dup ⟨0, by decide⟩),
   pushAt 2042 2 2694,
   opAt 2043 .JUMPI]

/-- `after_sq` (pc 3303): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2044 .POP,
   pushAt 2045 2 1147,
   pushAt 2046 2 256,
   opAt 2047 (.Dup ⟨0, by decide⟩),
   pushAt 2048 2 512,
   pushAt 2049 2 3547,
   opAt 2050 .JUMP]

def fallback : List Located :=
  [opAt 2051 .JUMPDEST,
   opAt 2052 (.Dup ⟨0, by decide⟩),
   pushAt 2053 2 1024,
   pushAt 2054 2 256,
   opAt 2055 .MCOPY,
   pushAt 2056 0 0,
   pushAt 2057 2 1048,
   opAt 2058 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2637 = true :=
  Artifact.isValidJumpDest_index 1992 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2674 = true :=
  Artifact.isValidJumpDest_index 2015 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2694 = true :=
  Artifact.isValidJumpDest_index 2026 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2715 = true :=
  Artifact.isValidJumpDest_index 2037 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2739 = true :=
  Artifact.isValidJumpDest_index 2051 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3547 = true :=
  Artifact.isValidJumpDest_index 2657 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3551 = true :=
  Artifact.isValidJumpDest_index 2659 (by rfl)


/- `after_sq` (pc 3303): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
