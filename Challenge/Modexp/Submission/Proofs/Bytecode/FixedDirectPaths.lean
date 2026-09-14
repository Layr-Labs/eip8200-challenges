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

@[simp] theorem directPC0 (i : Nat) (hi : 1843 ≤ i) (hii : i ≤ 1876) :
    Artifact.submissionArtifact.instructionPC i =
      ([2439,2440,2441,2443,2444,2447,2448,2449,2451,2452,2455,2456,2459,2460,2461,2462,2463,2465,2466,2469,2470,2472,2475,2476,2477,2480,2481,2482,2484,2485,2489,2490,2493,2494] : List Nat)[i - 1843]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 1877 ≤ i) (hii : i ≤ 1909) :
    Artifact.submissionArtifact.instructionPC i =
      ([2496,2497,2498,2501,2502,2505,2508,2509,2510,2513,2516,2517,2518,2519,2520,2521,2522,2525,2526,2527,2530,2533,2534,2537,2540,2541,2542,2543,2546,2549,2550,2551,2554] : List Nat)[i - 1877]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1866 .JUMPDEST,
   pushAt 1867 2 2816,
   opAt 1868 .MLOAD,
   opAt 1869 .CALLDATALOAD,
   pushAt 1870 1 232,
   opAt 1871 .SHR,
   pushAt 1872 3 65537,
   opAt 1873 .XOR,
   pushAt 1874 2 2541,
   opAt 1875 .JUMPI]

def checkThree : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1854 2 2816,
   opAt 1855 .MLOAD,
   opAt 1856 .CALLDATALOAD,
   pushAt 1857 0 0,
   opAt 1858 .BYTE,
   pushAt 1859 1 3,
   opAt 1860 .XOR,
   pushAt 1861 2 2541,
   opAt 1862 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1843 .JUMPDEST,
   opAt 1844 (.Dup ⟨3, by decide⟩),
   pushAt 1845 1 3,
   opAt 1846 .EQ,
   pushAt 1847 2 2476,
   opAt 1848 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1876 1 16]

def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1849 (.Dup ⟨3, by decide⟩),
   pushAt 1850 1 1,
   opAt 1851 .XOR,
   pushAt 1852 2 2541,
   opAt 1853 .JUMPI]

def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1863 1 1,
   pushAt 1864 2 2496,
   opAt 1865 .JUMP]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3294. -/
def squareCall : List Located :=
  [opAt 1877 .JUMPDEST,
   opAt 1878 (.Dup ⟨0, by decide⟩),
   pushAt 1879 2 2624,
   opAt 1880 .MSTORE,
   pushAt 1881 2 2517,
   pushAt 1882 2 512,
   opAt 1883 (.Dup ⟨0, by decide⟩),
   opAt 1884 (.Dup ⟨0, by decide⟩),
   pushAt 1885 2 4564,
   pushAt 1886 2 3353,
   opAt 1887 .JUMP]

def squareReturn : List Located :=
  [opAt 1888 .JUMPDEST,
   pushAt 1889 0 0,
   opAt 1890 .NOT,
   opAt 1891 .ADD,
   opAt 1892 (.Dup ⟨0, by decide⟩),
   pushAt 1893 2 2496,
   opAt 1894 .JUMPI]

/-- `after_sq` (pc 3304): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 1895 .POP,
   pushAt 1896 2 1037,
   pushAt 1897 2 256,
   opAt 1898 (.Dup ⟨0, by decide⟩),
   pushAt 1899 2 512,
   pushAt 1900 2 3349,
   opAt 1901 .JUMP]

def fallback : List Located :=
  [opAt 1902 .JUMPDEST,
   opAt 1903 (.Dup ⟨0, by decide⟩),
   pushAt 1904 2 1024,
   pushAt 1905 2 256,
   opAt 1906 .MCOPY,
   pushAt 1907 0 0,
   pushAt 1908 2 937,
   opAt 1909 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2439 = true :=
  Artifact.isValidJumpDest_index 1843 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2476 = true :=
  Artifact.isValidJumpDest_index 1866 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2496 = true :=
  Artifact.isValidJumpDest_index 1877 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2517 = true :=
  Artifact.isValidJumpDest_index 1888 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2541 = true :=
  Artifact.isValidJumpDest_index 1902 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3349 = true :=
  Artifact.isValidJumpDest_index 2509 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3353 = true :=
  Artifact.isValidJumpDest_index 2511 (by rfl)


/- `after_sq` (pc 3304): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
