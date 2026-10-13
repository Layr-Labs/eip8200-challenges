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
loop head passes the square count minus one in the kernel frame's `pdst` slot.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 1974 ≤ i) (hii : i ≤ 2007) :
    Artifact.submissionArtifact.instructionPC i =
      ([2492,2493,2494,2496,2497,2500,2501,2502,2504,2505,2508,2509,2510,2511,2512,2514,2515,2516,2519,2520,2521,2523,2526,2527,2528,2531,2532,2533,2535,2536,2540,2541,2544,2545] : List Nat)[i - 1974]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 2008 ≤ i) (hii : i ≤ 2018) :
    Artifact.submissionArtifact.instructionPC i =
      ([2547,2548,2551,2552,2553,2554,2555,2558,2561,2564,2567] : List Nat)[i - 2008]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1997 .JUMPDEST,
   pushAt 1998 2 2816,
   opAt 1999 .MLOAD,
   opAt 2000 .CALLDATALOAD,
   pushAt 2001 1 232,
   opAt 2002 .SHR,
   pushAt 2003 3 65537,
   opAt 2004 .XOR,
   pushAt 2005 2 790,
   opAt 2006 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1974 .JUMPDEST,
   opAt 1975 (.Dup ⟨3, by decide⟩),
   pushAt 1976 1 3,
   opAt 1977 .EQ,
   pushAt 1978 2 2527,
   opAt 1979 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2007 1 16]

/-- The merged one-byte-exponent test (pcs 2450-2470): `(esize ^ 1) | (e[0] ^ 3)`, nonzero
bails to `BAIL6` (790); zero falls through into `e3go` (2471). -/
def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1980 (.Dup ⟨3, by decide⟩),
   pushAt 1981 1 1,
   opAt 1982 .XOR,
   pushAt 1983 2 2816,
   opAt 1984 .MLOAD,
   opAt 1985 .CALLDATALOAD,
   pushAt 1986 0 0,
   opAt 1987 .BYTE,
   pushAt 1988 1 3,
   opAt 1989 .XOR,
   opAt 1990 .OR,
   pushAt 1991 2 790,
   opAt 1992 .JUMPI]

/-- `e3go` (pcs 2471-2477): the E3 hit, square count `1`, jump to the loop head 2498.  Entered
by falling through the merged test, and by the shift cleanup tail after the E3 phase switch. -/
def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1993 .JUMPDEST,
   pushAt 1994 1 1,
   pushAt 1995 2 2547,
   opAt 1996 .JUMP]

def start : List Located :=
  []

/-- Loop head: put the remaining square count minus one in the kernel frame's
`pdst` slot (the in-kernel loop counts it down) and call `SQUARE(0x840) → 0x200`,
entering the kernel's `common` block with `hd = sq_row` and return address 2519. -/
def squareCall : List Located :=
  [opAt 2008 .JUMPDEST,
   pushAt 2009 2 2519,
   pushAt 2010 0 0,
   opAt 2011 .NOT,
   opAt 2012 (.Dup ⟨2, by decide⟩),
   opAt 2013 .ADD,
   pushAt 2014 2 512,
   pushAt 2015 2 2112,
   pushAt 2016 2 4582,
   pushAt 2017 2 3405,
   opAt 2018 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2492 = true :=
  Artifact.isValidJumpDest_index 1974 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2527 = true :=
  Artifact.isValidJumpDest_index 1997 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2547 = true :=
  Artifact.isValidJumpDest_index 2008 (by rfl)

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

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3405 = true :=
  Artifact.isValidJumpDest_index 2657 (by rfl)


/- `after_sq` (pc 3304): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
