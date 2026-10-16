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

@[simp] theorem directPC0 (i : Nat) (hi : 1835 ≤ i) (hii : i ≤ 1866) :
    Artifact.submissionArtifact.instructionPC i =
      ([2317,2318,2319,2321,2322,2325,2326,2328,2329,2330,2332,2335,2336,2337,2339,2340,2341,2342,2345,2346,2349,2350,2351,2354,2355,2356,2358,2359,2363,2364,2366,2367] : List Nat)[i - 1835]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 1867 ≤ i) (hii : i ≤ 1877) :
    Artifact.submissionArtifact.instructionPC i =
      ([2369,2370,2373,2374,2375,2376,2377,2380,2383,2386,2389] : List Nat)[i - 1867]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1856 .JUMPDEST,
   pushAt 1857 2 2656,
   opAt 1858 .MLOAD,
   opAt 1859 .CALLDATALOAD,
   pushAt 1860 1 232,
   opAt 1861 .SHR,
   pushAt 1862 3 65537,
   opAt 1863 .XOR,
   pushAt 1864 1 219,
   opAt 1865 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1835 .JUMPDEST,
   opAt 1836 (.Dup ⟨3, by decide⟩),
   pushAt 1837 1 3,
   opAt 1838 .EQ,
   pushAt 1839 2 2350,
   opAt 1840 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1866 1 16]

/-- Every exponent width but three (pc 2326) jumps to `modexpBig` (219). -/
def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1841 1 219,
   opAt 1842 .JUMP]

/-- `e3go` (pc 2329): the E3 hit, square count `1`, jump to the loop head.  Entered by the shift
cleanup tail after the E3 phase switch. -/
def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1843 .JUMPDEST,
   pushAt 1844 1 1,
   pushAt 1845 2 2369,
   opAt 1846 .JUMP]

def start : List Located :=
  []

/-- Loop head: put the remaining square count minus one in the kernel frame's
`pdst` slot (the in-kernel loop counts it down) and call `SQUARE(0x840) → 0x200`,
entering the kernel's `common` block with `hd = sq_row` and return address 2519. -/
def squareCall : List Located :=
  [opAt 1867 .JUMPDEST,
   pushAt 1868 2 2519,
   pushAt 1869 0 0,
   opAt 1870 .NOT,
   opAt 1871 (.Dup ⟨2, by decide⟩),
   opAt 1872 .ADD,
   pushAt 1873 2 512,
   pushAt 1874 2 2112,
   pushAt 1875 2 4245,
   pushAt 1876 2 3181,
   opAt 1877 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2317 = true :=
  Artifact.isValidJumpDest_index 1835 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2350 = true :=
  Artifact.isValidJumpDest_index 1856 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2369 = true :=
  Artifact.isValidJumpDest_index 1867 (by rfl)

/-- `modexpBig` (pc 219), the target of every recogniser miss. -/
theorem jumpDestBail :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 219 = true :=
  Artifact.isValidJumpDest_index 146 (by rfl)

/-- `modexpBig` (pc 237), where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 219 = true :=
  Artifact.isValidJumpDest_index 146 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3181 = true :=
  Artifact.isValidJumpDest_index 2478 (by rfl)


/- `after_sq` (pc 3304): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
