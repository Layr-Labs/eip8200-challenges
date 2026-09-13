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

@[simp] theorem directPC0 (i : Nat) (hi : 1989 ≤ i) (hii : i ≤ 2022) :
    Artifact.submissionArtifact.instructionPC i =
      ([2638,2639,2640,2642,2643,2646,2647,2648,2650,2651,2654,2655,2658,2659,2660,2661,2662,2664,2665,2668,2669,2671,2674,2675,2676,2679,2680,2681,2683,2684,2688,2689,2692,2693] : List Nat)[i - 1989]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 2023 ≤ i) (hii : i ≤ 2055) :
    Artifact.submissionArtifact.instructionPC i =
      ([2695,2696,2697,2700,2701,2704,2707,2708,2709,2712,2715,2716,2717,2718,2719,2720,2721,2724,2725,2726,2729,2732,2733,2736,2739,2740,2741,2742,2745,2748,2749,2750,2753] : List Nat)[i - 2023]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2012 .JUMPDEST,
   pushAt 2013 2 2816,
   opAt 2014 .MLOAD,
   opAt 2015 .CALLDATALOAD,
   pushAt 2016 1 232,
   opAt 2017 .SHR,
   pushAt 2018 3 65537,
   opAt 2019 .XOR,
   pushAt 2020 2 2740,
   opAt 2021 .JUMPI]

def checkThree : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2000 2 2816,
   opAt 2001 .MLOAD,
   opAt 2002 .CALLDATALOAD,
   pushAt 2003 0 0,
   opAt 2004 .BYTE,
   pushAt 2005 1 3,
   opAt 2006 .XOR,
   pushAt 2007 2 2740,
   opAt 2008 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1989 .JUMPDEST,
   opAt 1990 (.Dup ⟨3, by decide⟩),
   pushAt 1991 1 3,
   opAt 1992 .EQ,
   pushAt 1993 2 2675,
   opAt 1994 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2022 1 16]

def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1995 (.Dup ⟨3, by decide⟩),
   pushAt 1996 1 1,
   opAt 1997 .XOR,
   pushAt 1998 2 2740,
   opAt 1999 .JUMPI]

def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2009 1 1,
   pushAt 2010 2 2695,
   opAt 2011 .JUMP]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3294. -/
def squareCall : List Located :=
  [opAt 2023 .JUMPDEST,
   opAt 2024 (.Dup ⟨0, by decide⟩),
   pushAt 2025 2 2624,
   opAt 2026 .MSTORE,
   pushAt 2027 2 2716,
   pushAt 2028 2 512,
   opAt 2029 (.Dup ⟨0, by decide⟩),
   opAt 2030 (.Dup ⟨0, by decide⟩),
   pushAt 2031 2 4759,
   pushAt 2032 2 3556,
   opAt 2033 .JUMP]

def squareReturn : List Located :=
  [opAt 2034 .JUMPDEST,
   pushAt 2035 0 0,
   opAt 2036 .NOT,
   opAt 2037 .ADD,
   opAt 2038 (.Dup ⟨0, by decide⟩),
   pushAt 2039 2 2695,
   opAt 2040 .JUMPI]

/-- `after_sq` (pc 3303): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2041 .POP,
   pushAt 2042 2 1148,
   pushAt 2043 2 256,
   opAt 2044 (.Dup ⟨0, by decide⟩),
   pushAt 2045 2 512,
   pushAt 2046 2 3552,
   opAt 2047 .JUMP]

def fallback : List Located :=
  [opAt 2048 .JUMPDEST,
   opAt 2049 (.Dup ⟨0, by decide⟩),
   pushAt 2050 2 1024,
   pushAt 2051 2 256,
   opAt 2052 .MCOPY,
   pushAt 2053 0 0,
   pushAt 2054 2 1049,
   opAt 2055 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2638 = true :=
  Artifact.isValidJumpDest_index 1989 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2675 = true :=
  Artifact.isValidJumpDest_index 2012 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2695 = true :=
  Artifact.isValidJumpDest_index 2023 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2716 = true :=
  Artifact.isValidJumpDest_index 2034 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2740 = true :=
  Artifact.isValidJumpDest_index 2048 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3552 = true :=
  Artifact.isValidJumpDest_index 2658 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3556 = true :=
  Artifact.isValidJumpDest_index 2660 (by rfl)


/- `after_sq` (pc 3303): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
