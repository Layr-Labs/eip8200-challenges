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

@[simp] theorem directPC0 (i : Nat) (hi : 1982 ≤ i) (hii : i ≤ 2015) :
    Artifact.submissionArtifact.instructionPC i =
      ([2636,2637,2638,2640,2641,2644,2645,2646,2648,2649,2652,2653,2656,2657,2658,2659,2660,2662,2663,2666,2667,2669,2672,2673,2674,2677,2678,2679,2681,2682,2686,2687,2690,2691] : List Nat)[i - 1982]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 2016 ≤ i) (hii : i ≤ 2048) :
    Artifact.submissionArtifact.instructionPC i =
      ([2693,2694,2695,2698,2699,2702,2705,2706,2707,2710,2713,2714,2715,2716,2717,2718,2719,2722,2723,2724,2727,2730,2731,2734,2737,2738,2739,2740,2743,2746,2747,2748,2751] : List Nat)[i - 2016]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2005 .JUMPDEST,
   pushAt 2006 2 2816,
   opAt 2007 .MLOAD,
   opAt 2008 .CALLDATALOAD,
   pushAt 2009 1 232,
   opAt 2010 .SHR,
   pushAt 2011 3 65537,
   opAt 2012 .XOR,
   pushAt 2013 2 2738,
   opAt 2014 .JUMPI]

def checkThree : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1993 2 2816,
   opAt 1994 .MLOAD,
   opAt 1995 .CALLDATALOAD,
   pushAt 1996 0 0,
   opAt 1997 .BYTE,
   pushAt 1998 1 3,
   opAt 1999 .XOR,
   pushAt 2000 2 2738,
   opAt 2001 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1982 .JUMPDEST,
   opAt 1983 (.Dup ⟨3, by decide⟩),
   pushAt 1984 1 3,
   opAt 1985 .EQ,
   pushAt 1986 2 2673,
   opAt 1987 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2015 1 16]

def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1988 (.Dup ⟨3, by decide⟩),
   pushAt 1989 1 1,
   opAt 1990 .XOR,
   pushAt 1991 2 2738,
   opAt 1992 .JUMPI]

def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2002 1 1,
   pushAt 2003 2 2693,
   opAt 2004 .JUMP]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3294. -/
def squareCall : List Located :=
  [opAt 2016 .JUMPDEST,
   opAt 2017 (.Dup ⟨0, by decide⟩),
   pushAt 2018 2 2624,
   opAt 2019 .MSTORE,
   pushAt 2020 2 2714,
   pushAt 2021 2 512,
   opAt 2022 (.Dup ⟨0, by decide⟩),
   opAt 2023 (.Dup ⟨0, by decide⟩),
   pushAt 2024 2 4770,
   pushAt 2025 2 3550,
   opAt 2026 .JUMP]

def squareReturn : List Located :=
  [opAt 2027 .JUMPDEST,
   pushAt 2028 0 0,
   opAt 2029 .NOT,
   opAt 2030 .ADD,
   opAt 2031 (.Dup ⟨0, by decide⟩),
   pushAt 2032 2 2693,
   opAt 2033 .JUMPI]

/-- `after_sq` (pc 3304): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2034 .POP,
   pushAt 2035 2 1148,
   pushAt 2036 2 256,
   opAt 2037 (.Dup ⟨0, by decide⟩),
   pushAt 2038 2 512,
   pushAt 2039 2 3546,
   opAt 2040 .JUMP]

def fallback : List Located :=
  [opAt 2041 .JUMPDEST,
   opAt 2042 (.Dup ⟨0, by decide⟩),
   pushAt 2043 2 1024,
   pushAt 2044 2 256,
   opAt 2045 .MCOPY,
   pushAt 2046 0 0,
   pushAt 2047 2 1048,
   opAt 2048 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2636 = true :=
  Artifact.isValidJumpDest_index 1982 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2673 = true :=
  Artifact.isValidJumpDest_index 2005 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2693 = true :=
  Artifact.isValidJumpDest_index 2016 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2714 = true :=
  Artifact.isValidJumpDest_index 2027 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2738 = true :=
  Artifact.isValidJumpDest_index 2041 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3546 = true :=
  Artifact.isValidJumpDest_index 2648 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3550 = true :=
  Artifact.isValidJumpDest_index 2650 (by rfl)


/- `after_sq` (pc 3304): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
