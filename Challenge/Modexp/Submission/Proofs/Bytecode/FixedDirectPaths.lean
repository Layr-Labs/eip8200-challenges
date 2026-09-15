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

@[simp] theorem directPC0 (i : Nat) (hi : 1845 ≤ i) (hii : i ≤ 1878) :
    Artifact.submissionArtifact.instructionPC i =
      ([2443,2444,2445,2447,2448,2451,2452,2453,2455,2456,2459,2460,2463,2464,2465,2466,2467,2469,2470,2473,2474,2476,2479,2480,2481,2484,2485,2486,2488,2489,2493,2494,2497,2498] : List Nat)[i - 1845]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 1879 ≤ i) (hii : i ≤ 1911) :
    Artifact.submissionArtifact.instructionPC i =
      ([2500,2501,2502,2505,2506,2509,2512,2513,2514,2517,2520,2521,2522,2523,2524,2525,2526,2529,2530,2531,2534,2537,2538,2541,2544,2545,2546,2547,2550,2553,2554,2555,2558] : List Nat)[i - 1879]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1868 .JUMPDEST,
   pushAt 1869 2 2816,
   opAt 1870 .MLOAD,
   opAt 1871 .CALLDATALOAD,
   pushAt 1872 1 232,
   opAt 1873 .SHR,
   pushAt 1874 3 65537,
   opAt 1875 .XOR,
   pushAt 1876 2 2545,
   opAt 1877 .JUMPI]

def checkThree : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1856 2 2816,
   opAt 1857 .MLOAD,
   opAt 1858 .CALLDATALOAD,
   pushAt 1859 0 0,
   opAt 1860 .BYTE,
   pushAt 1861 1 3,
   opAt 1862 .XOR,
   pushAt 1863 2 2545,
   opAt 1864 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1845 .JUMPDEST,
   opAt 1846 (.Dup ⟨3, by decide⟩),
   pushAt 1847 1 3,
   opAt 1848 .EQ,
   pushAt 1849 2 2480,
   opAt 1850 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1878 1 16]

def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1851 (.Dup ⟨3, by decide⟩),
   pushAt 1852 1 1,
   opAt 1853 .XOR,
   pushAt 1854 2 2545,
   opAt 1855 .JUMPI]

def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1865 1 1,
   pushAt 1866 2 2500,
   opAt 1867 .JUMP]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3294. -/
def squareCall : List Located :=
  [opAt 1879 .JUMPDEST,
   opAt 1880 (.Dup ⟨0, by decide⟩),
   pushAt 1881 2 2624,
   opAt 1882 .MSTORE,
   pushAt 1883 2 2521,
   pushAt 1884 2 512,
   opAt 1885 (.Dup ⟨0, by decide⟩),
   opAt 1886 (.Dup ⟨0, by decide⟩),
   pushAt 1887 2 4568,
   pushAt 1888 2 3357,
   opAt 1889 .JUMP]

def squareReturn : List Located :=
  [opAt 1890 .JUMPDEST,
   pushAt 1891 0 0,
   opAt 1892 .NOT,
   opAt 1893 .ADD,
   opAt 1894 (.Dup ⟨0, by decide⟩),
   pushAt 1895 2 2500,
   opAt 1896 .JUMPI]

/-- `after_sq` (pc 3304): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 1897 .POP,
   pushAt 1898 2 1038,
   pushAt 1899 2 256,
   opAt 1900 (.Dup ⟨0, by decide⟩),
   pushAt 1901 2 512,
   pushAt 1902 2 3353,
   opAt 1903 .JUMP]

def fallback : List Located :=
  [opAt 1904 .JUMPDEST,
   opAt 1905 (.Dup ⟨0, by decide⟩),
   pushAt 1906 2 1024,
   pushAt 1907 2 256,
   opAt 1908 .MCOPY,
   pushAt 1909 0 0,
   pushAt 1910 2 939,
   opAt 1911 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2443 = true :=
  Artifact.isValidJumpDest_index 1845 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2480 = true :=
  Artifact.isValidJumpDest_index 1868 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2500 = true :=
  Artifact.isValidJumpDest_index 1879 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2521 = true :=
  Artifact.isValidJumpDest_index 1890 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2545 = true :=
  Artifact.isValidJumpDest_index 1904 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3353 = true :=
  Artifact.isValidJumpDest_index 2510 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3357 = true :=
  Artifact.isValidJumpDest_index 2512 (by rfl)


/- `after_sq` (pc 3304): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
