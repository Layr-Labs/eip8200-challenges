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

@[simp] theorem directPC0 (i : Nat) (hi : 1993 ≤ i) (hii : i ≤ 2026) :
    Artifact.submissionArtifact.instructionPC i =
      ([2638,2639,2640,2642,2643,2646,2647,2648,2650,2651,2654,2655,2658,2659,2660,2661,2662,2664,2665,2668,2669,2671,2674,2675,2676,2679,2680,2681,2683,2684,2688,2689,2692,2693] : List Nat)[i - 1993]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 2027 ≤ i) (hii : i ≤ 2059) :
    Artifact.submissionArtifact.instructionPC i =
      ([2695,2696,2697,2700,2701,2704,2707,2708,2709,2712,2715,2716,2717,2718,2719,2720,2721,2724,2725,2726,2729,2732,2733,2736,2739,2740,2741,2742,2745,2748,2749,2750,2753] : List Nat)[i - 2027]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2016 .JUMPDEST,
   pushAt 2017 2 2816,
   opAt 2018 .MLOAD,
   opAt 2019 .CALLDATALOAD,
   pushAt 2020 1 232,
   opAt 2021 .SHR,
   pushAt 2022 3 65537,
   opAt 2023 .XOR,
   pushAt 2024 2 2740,
   opAt 2025 .JUMPI]

def checkThree : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2004 2 2816,
   opAt 2005 .MLOAD,
   opAt 2006 .CALLDATALOAD,
   pushAt 2007 0 0,
   opAt 2008 .BYTE,
   pushAt 2009 1 3,
   opAt 2010 .XOR,
   pushAt 2011 2 2740,
   opAt 2012 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1993 .JUMPDEST,
   opAt 1994 (.Dup ⟨3, by decide⟩),
   pushAt 1995 1 3,
   opAt 1996 .EQ,
   pushAt 1997 2 2675,
   opAt 1998 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2026 1 16]

def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1999 (.Dup ⟨3, by decide⟩),
   pushAt 2000 1 1,
   opAt 2001 .XOR,
   pushAt 2002 2 2740,
   opAt 2003 .JUMPI]

def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2013 1 1,
   pushAt 2014 2 2695,
   opAt 2015 .JUMP]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3294. -/
def squareCall : List Located :=
  [opAt 2027 .JUMPDEST,
   opAt 2028 (.Dup ⟨0, by decide⟩),
   pushAt 2029 2 2624,
   opAt 2030 .MSTORE,
   pushAt 2031 2 2716,
   pushAt 2032 2 512,
   opAt 2033 (.Dup ⟨0, by decide⟩),
   opAt 2034 (.Dup ⟨0, by decide⟩),
   pushAt 2035 2 4757,
   pushAt 2036 2 3554,
   opAt 2037 .JUMP]

def squareReturn : List Located :=
  [opAt 2038 .JUMPDEST,
   pushAt 2039 0 0,
   opAt 2040 .NOT,
   opAt 2041 .ADD,
   opAt 2042 (.Dup ⟨0, by decide⟩),
   pushAt 2043 2 2695,
   opAt 2044 .JUMPI]

/-- `after_sq` (pc 3303): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2045 .POP,
   pushAt 2046 2 1148,
   pushAt 2047 2 256,
   opAt 2048 (.Dup ⟨0, by decide⟩),
   pushAt 2049 2 512,
   pushAt 2050 2 3550,
   opAt 2051 .JUMP]

def fallback : List Located :=
  [opAt 2052 .JUMPDEST,
   opAt 2053 (.Dup ⟨0, by decide⟩),
   pushAt 2054 2 1024,
   pushAt 2055 2 256,
   opAt 2056 .MCOPY,
   pushAt 2057 0 0,
   pushAt 2058 2 1049,
   opAt 2059 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2638 = true :=
  Artifact.isValidJumpDest_index 1993 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2675 = true :=
  Artifact.isValidJumpDest_index 2016 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2695 = true :=
  Artifact.isValidJumpDest_index 2027 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2716 = true :=
  Artifact.isValidJumpDest_index 2038 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2740 = true :=
  Artifact.isValidJumpDest_index 2052 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3550 = true :=
  Artifact.isValidJumpDest_index 2660 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3554 = true :=
  Artifact.isValidJumpDest_index 2662 (by rfl)


/- `after_sq` (pc 3303): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
