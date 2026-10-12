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

@[simp] theorem directPC0 (i : Nat) (hi : 1933 ≤ i) (hii : i ≤ 1966) :
    Artifact.submissionArtifact.instructionPC i =
      ([2441,2442,2443,2445,2446,2449,2450,2451,2453,2454,2457,2458,2461,2462,2463,2464,2465,2467,2468,2471,2472,2474,2477,2478,2479,2482,2483,2484,2486,2487,2491,2492,2495,2496] : List Nat)[i - 1933]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 1967 ≤ i) (hii : i ≤ 1991) :
    Artifact.submissionArtifact.instructionPC i =
      ([2498,2499,2500,2503,2504,2507,2510,2511,2514,2517,2520,2521,2522,2523,2524,2525,2526,2529,2530,2531,2534,2537,2538,2541,2544] : List Nat)[i - 1967]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1956 .JUMPDEST,
   pushAt 1957 2 2816,
   opAt 1958 .MLOAD,
   opAt 1959 .CALLDATALOAD,
   pushAt 1960 1 232,
   opAt 1961 .SHR,
   pushAt 1962 3 65537,
   opAt 1963 .XOR,
   pushAt 1964 2 790,
   opAt 1965 .JUMPI]

def checkThree : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1944 2 2816,
   opAt 1945 .MLOAD,
   opAt 1946 .CALLDATALOAD,
   pushAt 1947 0 0,
   opAt 1948 .BYTE,
   pushAt 1949 1 3,
   opAt 1950 .XOR,
   pushAt 1951 2 790,
   opAt 1952 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1933 .JUMPDEST,
   opAt 1934 (.Dup ⟨3, by decide⟩),
   pushAt 1935 1 3,
   opAt 1936 .EQ,
   pushAt 1937 2 2478,
   opAt 1938 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1966 1 16]

def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1939 (.Dup ⟨3, by decide⟩),
   pushAt 1940 1 1,
   opAt 1941 .XOR,
   pushAt 1942 2 790,
   opAt 1943 .JUMPI]

def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1953 1 1,
   pushAt 1954 2 2498,
   opAt 1955 .JUMP]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3292. -/
def squareCall : List Located :=
  [opAt 1967 .JUMPDEST,
   opAt 1968 (.Dup ⟨0, by decide⟩),
   pushAt 1969 2 2624,
   opAt 1970 .MSTORE,
   pushAt 1971 2 2519,
   pushAt 1972 2 512,
   opAt 1973 (.Dup ⟨0, by decide⟩),
   pushAt 1974 2 2112,
   pushAt 1975 2 4551,
   pushAt 1976 2 3387,
   opAt 1977 .JUMP]

def squareReturn : List Located :=
  [opAt 1978 .JUMPDEST,
   pushAt 1979 0 0,
   opAt 1980 .NOT,
   opAt 1981 .ADD,
   opAt 1982 (.Dup ⟨0, by decide⟩),
   pushAt 1983 2 2498,
   opAt 1984 .JUMPI]

/-- `after_sq` (pc 3304): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 1985 .POP,
   pushAt 1986 2 774,
   pushAt 1987 2 256,
   opAt 1988 (.Dup ⟨0, by decide⟩),
   pushAt 1989 2 512,
   pushAt 1990 2 5466,
   opAt 1991 .JUMP]


theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2441 = true :=
  Artifact.isValidJumpDest_index 1933 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2478 = true :=
  Artifact.isValidJumpDest_index 1956 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2498 = true :=
  Artifact.isValidJumpDest_index 1967 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2521 = true :=
  Artifact.isValidJumpDest_index 1978 (by rfl)

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

/-- The kernel's multiply entry trampoline `0x155a` (the final mixed-domain product): it
clears the product block and jumps to the multiply entry `0x0d37`. -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5466 = true :=
  Artifact.isValidJumpDest_index 4302 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3387 = true :=
  Artifact.isValidJumpDest_index 2621 (by rfl)


/- `after_sq` (pc 3304): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
