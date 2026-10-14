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

@[simp] theorem directPC0 (i : Nat) (hi : 1893 ≤ i) (hii : i ≤ 1926) :
    Artifact.submissionArtifact.instructionPC i =
      ([2389,2390,2391,2393,2394,2397,2398,2399,2401,2402,2405,2406,2407,2408,2409,2411,2412,2413,2416,2417,2418,2420,2423,2424,2425,2428,2429,2430,2432,2433,2437,2438,2441,2442] : List Nat)[i - 1893]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 1927 ≤ i) (hii : i ≤ 1937) :
    Artifact.submissionArtifact.instructionPC i =
      ([2444,2445,2448,2449,2450,2451,2452,2455,2458,2461,2464] : List Nat)[i - 1927]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1916 .JUMPDEST,
   pushAt 1917 2 2816,
   opAt 1918 .MLOAD,
   opAt 1919 .CALLDATALOAD,
   pushAt 1920 1 232,
   opAt 1921 .SHR,
   pushAt 1922 3 65537,
   opAt 1923 .XOR,
   pushAt 1924 2 761,
   opAt 1925 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1893 .JUMPDEST,
   opAt 1894 (.Dup ⟨3, by decide⟩),
   pushAt 1895 1 3,
   opAt 1896 .EQ,
   pushAt 1897 2 2424,
   opAt 1898 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1926 1 16]

/-- The merged one-byte-exponent test (pcs 2450-2470): `(esize ^ 1) | (e[0] ^ 3)`, nonzero
bails to `BAIL6` (790); zero falls through into `e3go` (2471). -/
def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1899 (.Dup ⟨3, by decide⟩),
   pushAt 1900 1 1,
   opAt 1901 .XOR,
   pushAt 1902 2 2816,
   opAt 1903 .MLOAD,
   opAt 1904 .CALLDATALOAD,
   pushAt 1905 0 0,
   opAt 1906 .BYTE,
   pushAt 1907 1 3,
   opAt 1908 .XOR,
   opAt 1909 .OR,
   pushAt 1910 2 761,
   opAt 1911 .JUMPI]

/-- `e3go` (pcs 2471-2477): the E3 hit, square count `1`, jump to the loop head 2498.  Entered
by falling through the merged test, and by the shift cleanup tail after the E3 phase switch. -/
def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1912 .JUMPDEST,
   pushAt 1913 1 1,
   pushAt 1914 2 2444,
   opAt 1915 .JUMP]

def start : List Located :=
  []

/-- Loop head: put the remaining square count minus one in the kernel frame's
`pdst` slot (the in-kernel loop counts it down) and call `SQUARE(0x840) → 0x200`,
entering the kernel's `common` block with `hd = sq_row` and return address 2519. -/
def squareCall : List Located :=
  [opAt 1927 .JUMPDEST,
   pushAt 1928 2 2519,
   pushAt 1929 0 0,
   opAt 1930 .NOT,
   opAt 1931 (.Dup ⟨2, by decide⟩),
   opAt 1932 .ADD,
   pushAt 1933 2 512,
   pushAt 1934 2 2112,
   pushAt 1935 2 4268,
   pushAt 1936 2 3189,
   opAt 1937 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2389 = true :=
  Artifact.isValidJumpDest_index 1893 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2424 = true :=
  Artifact.isValidJumpDest_index 1916 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2444 = true :=
  Artifact.isValidJumpDest_index 1927 (by rfl)

/-- `BAIL6` (pc 1054), the target of all three recogniser misses. -/
theorem jumpDestBail :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 761 = true :=
  Artifact.isValidJumpDest_index 545 (by rfl)

/-- `modexpBig` (pc 237), where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 218 = true :=
  Artifact.isValidJumpDest_index 148 (by rfl)

theorem pcTramp717 : Artifact.submissionArtifact.instructionPC 545 = 761 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem pcTramp718 : Artifact.submissionArtifact.instructionPC 546 = 762 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem pcTramp719 : Artifact.submissionArtifact.instructionPC 547 = 764 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

/-- The six-word bail trampoline: `JUMPDEST; PUSH1 237; JUMP`. -/
def bail : List Located :=
  [opAt 545 .JUMPDEST,
   pushAt 546 1 218,
   opAt 547 .JUMP]

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3189 = true :=
  Artifact.isValidJumpDest_index 2492 (by rfl)


/- `after_sq` (pc 3304): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
