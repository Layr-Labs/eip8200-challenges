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

@[simp] theorem directPC0 (i : Nat) (hi : 1986 ≤ i) (hii : i ≤ 2019) :
    Artifact.submissionArtifact.instructionPC i =
      ([2396,2397,2398,2400,2401,2404,2405,2406,2408,2409,2412,2413,2416,2417,2418,2419,2420,2422,2423,2426,2427,2429,2432,2433,2434,2437,2438,2439,2441,2442,2446,2447,2450,2451] : List Nat)[i - 1986]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2009 .JUMPDEST,
   pushAt 2010 2 2816,
   opAt 2011 .MLOAD,
   opAt 2012 .CALLDATALOAD,
   pushAt 2013 1 232,
   opAt 2014 .SHR,
   pushAt 2015 3 65537,
   opAt 2016 .XOR,
   pushAt 2017 2 800,
   opAt 2018 .JUMPI]

def checkThree : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1997 2 2816,
   opAt 1998 .MLOAD,
   opAt 1999 .CALLDATALOAD,
   pushAt 2000 0 0,
   opAt 2001 .BYTE,
   pushAt 2002 1 3,
   opAt 2003 .XOR,
   pushAt 2004 2 800,
   opAt 2005 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1986 .JUMPDEST,
   opAt 1987 (.Dup ⟨3, by decide⟩),
   pushAt 1988 1 3,
   opAt 1989 .EQ,
   pushAt 1990 2 2433,
   opAt 1991 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2019 1 16]

def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1992 (.Dup ⟨3, by decide⟩),
   pushAt 1993 1 1,
   opAt 1994 .XOR,
   pushAt 1995 2 800,
   opAt 1996 .JUMPI]

def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2006 1 1,
   pushAt 2007 2 2453,
   opAt 2008 .JUMP]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3294. -/
def squareCall : List Located :=
  [opAt 2020 .JUMPDEST,
   opAt 2021 (.Dup ⟨0, by decide⟩),
   pushAt 2022 2 2624,
   opAt 2023 .MSTORE,
   pushAt 2024 2 800,
   pushAt 2025 2 512,
   opAt 2026 (.Dup ⟨0, by decide⟩),
   opAt 2027 (.Dup ⟨0, by decide⟩),
   pushAt 2028 2 4480,
   pushAt 2029 2 3327,
   opAt 2030 .JUMP]

/-- **S1b.** The six-word bail trampoline, located.  Transcribed from the
artifact: indices 578/579/580 are `JUMPDEST; PUSH1 0xee; JUMP` at pc 800/801/803,
and pc 238 is the wide-modulus fallback entry `modexpBig`.  This is the SAME
trampoline S1 proved for the 2350 class -- the three recogniser misses here push
800 directly, so nothing new is located and nothing new is assumed. -/
theorem pcTramp578 : Artifact.submissionArtifact.instructionPC 578 = 800 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem pcTramp579 : Artifact.submissionArtifact.instructionPC 579 = 801 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem pcTramp580 : Artifact.submissionArtifact.instructionPC 580 = 803 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- The trampoline head, the target of all three recogniser misses. -/
theorem jumpDestBail :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 800 = true :=
  Artifact.isValidJumpDest_index 578 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 238 = true :=
  Artifact.isValidJumpDest_index 165 (by rfl)

/-- The three-byte recogniser entry, reached from `entryPrefix` on `esize = 3`. -/
theorem jumpDestCheck65537 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2433 = true :=
  Artifact.isValidJumpDest_index 2009 (by rfl)

/-- The addition-chain head, reached from `threeHit` and `fermatHit`. -/
theorem jumpDestSpecial :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2453 = true :=
  Artifact.isValidJumpDest_index 2020 (by rfl)

/-- `JUMPDEST; PUSH1 0xee; JUMP`: the diverted recogniser miss.  It reads no
memory, takes no branch and consumes nothing beyond the target it pushes itself,
so the outer frame crosses unchanged and only `pc` moves. -/
def bail : List Located :=
  [opAt 578 .JUMPDEST,
   pushAt 579 1 238,
   opAt 580 .JUMP]

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
