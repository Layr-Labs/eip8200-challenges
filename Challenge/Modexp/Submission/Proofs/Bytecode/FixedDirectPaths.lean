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

@[simp] theorem directPC0 (i : Nat) (hi : 1995 ≤ i) (hii : i ≤ 2028) :
    Artifact.submissionArtifact.instructionPC i =
      ([2675,2676,2677,2679,2680,2683,2684,2685,2687,2688,2691,2692,2695,2696,2697,2698,2699,2701,2702,2705,2706,2708,2711,2712,2713,2716,2717,2718,2720,2721,2725,2726,2729,2730] : List Nat)[i - 1995]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2029 ≤ i) (hii : i ≤ 2062) :
    Artifact.submissionArtifact.instructionPC i =
      ([2732,2733,2734,2737,2738,2741,2744,2745,2746,2749,2752,2753,2754,2755,2756,2757,2758,2761,2762,2763,2764,2767,2770,2771,2774,2777,2778,2779,2780,2783,2786,2787,2788,2791] : List Nat)[i - 2029]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 1995 .JUMPDEST,
   opAt 1996 (.Dup ⟨3, by decide⟩),
   pushAt 1997 1 3,
   opAt 1998 .EQ,
   pushAt 1999 2 2712,
   opAt 2000 .JUMPI]

def oneWidth : List Located :=
  [opAt 2001 (.Dup ⟨3, by decide⟩),
   pushAt 2002 1 1,
   opAt 2003 .XOR,
   pushAt 2004 2 2778,
   opAt 2005 .JUMPI]

def checkThree : List Located :=
  [pushAt 2006 2 2816,
   opAt 2007 .MLOAD,
   opAt 2008 .CALLDATALOAD,
   pushAt 2009 0 0,
   opAt 2010 .BYTE,
   pushAt 2011 1 3,
   opAt 2012 .XOR,
   pushAt 2013 2 2778,
   opAt 2014 .JUMPI]

def threeHit : List Located :=
  [pushAt 2015 1 1,
   pushAt 2016 2 2732,
   opAt 2017 .JUMP]

def check65537 : List Located :=
  [opAt 2018 .JUMPDEST,
   pushAt 2019 2 2816,
   opAt 2020 .MLOAD,
   opAt 2021 .CALLDATALOAD,
   pushAt 2022 1 232,
   opAt 2023 .SHR,
   pushAt 2024 3 65537,
   opAt 2025 .XOR,
   pushAt 2026 2 2778,
   opAt 2027 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2028 1 16]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3294. -/
def squareCall : List Located :=
  [opAt 2029 .JUMPDEST,
   opAt 2030 (.Dup ⟨0, by decide⟩),
   pushAt 2031 2 2624,
   opAt 2032 .MSTORE,
   pushAt 2033 2 2753,
   pushAt 2034 2 512,
   opAt 2035 (.Dup ⟨0, by decide⟩),
   opAt 2036 (.Dup ⟨0, by decide⟩),
   pushAt 2037 2 4739,
   pushAt 2038 2 3537,
   opAt 2039 .JUMP]

def squareReturn : List Located :=
  [opAt 2040 .JUMPDEST,
   pushAt 2041 0 0,
   opAt 2042 .NOT,
   opAt 2043 .ADD,
   opAt 2044 (.Dup ⟨0, by decide⟩),
   pushAt 2045 2 2732,
   opAt 2046 .JUMPI]

/-- `after_sq` (pc 3303): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 2047 .JUMPDEST,
   opAt 2048 .POP,
   pushAt 2049 2 1160,
   pushAt 2050 2 256,
   opAt 2051 (.Dup ⟨0, by decide⟩),
   pushAt 2052 2 512,
   pushAt 2053 2 3533,
   opAt 2054 .JUMP]

def fallback : List Located :=
  [opAt 2055 .JUMPDEST,
   opAt 2056 (.Dup ⟨0, by decide⟩),
   pushAt 2057 2 1024,
   pushAt 2058 2 256,
   opAt 2059 .MCOPY,
   pushAt 2060 0 0,
   pushAt 2061 2 1061,
   opAt 2062 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2675 = true :=
  Artifact.isValidJumpDest_index 1995 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2712 = true :=
  Artifact.isValidJumpDest_index 2018 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2732 = true :=
  Artifact.isValidJumpDest_index 2029 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2753 = true :=
  Artifact.isValidJumpDest_index 2040 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2778 = true :=
  Artifact.isValidJumpDest_index 2055 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3533 = true :=
  Artifact.isValidJumpDest_index 2628 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3537 = true :=
  Artifact.isValidJumpDest_index 2630 (by rfl)


/-- `after_sq` (pc 3303): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/
theorem jumpDestAfterSq :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2762 = true :=
  Artifact.isValidJumpDest_index 2047 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
