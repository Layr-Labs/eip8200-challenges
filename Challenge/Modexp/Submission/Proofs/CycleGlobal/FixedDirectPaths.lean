import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PrefixPC
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs

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

namespace CycleSubmission.Global.FixedDirectPaths
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 1835 ≤ i) (hii : i ≤ 1866) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2317,2318,2319,2321,2322,2325,2326,2328,2329,2330,2332,2335,2336,2337,2339,2340,2341,2342,2345,2346,2349,2350,2351,2354,2355,2356,2358,2359,2363,2364,2366,2367] : List Nat)[i - 1835]! := by
  rw [CycleSubmission.Global.PrefixPC.eq_old i (by omega) (by omega)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths.directPC0 i hi hii

@[simp] theorem directPC1 (i : Nat) (hi : 1867 ≤ i) (hii : i ≤ 1876) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2369,2370,2373,2375,2376,2377,2380,2383,2386,2389] : List Nat)[i - 1867]! := by
  interval_cases i <;>
    rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength] <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [CycleSubmission.Global.Fast.opAt 1856 .JUMPDEST,
   CycleSubmission.Global.Fast.pushAt 1857 2 2656,
   CycleSubmission.Global.Fast.opAt 1858 .MLOAD,
   CycleSubmission.Global.Fast.opAt 1859 .CALLDATALOAD,
   CycleSubmission.Global.Fast.pushAt 1860 1 232,
   CycleSubmission.Global.Fast.opAt 1861 .SHR,
   CycleSubmission.Global.Fast.pushAt 1862 3 65537,
   CycleSubmission.Global.Fast.opAt 1863 .XOR,
   CycleSubmission.Global.Fast.pushAt 1864 1 219,
   CycleSubmission.Global.Fast.opAt 1865 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [CycleSubmission.Global.Fast.opAt 1835 .JUMPDEST,
   CycleSubmission.Global.Fast.opAt 1836 (.Dup ⟨3, by decide⟩),
   CycleSubmission.Global.Fast.pushAt 1837 1 3,
   CycleSubmission.Global.Fast.opAt 1838 .EQ,
   CycleSubmission.Global.Fast.pushAt 1839 2 2350,
   CycleSubmission.Global.Fast.opAt 1840 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [CycleSubmission.Global.Fast.pushAt 1866 1 16]

/-- Every exponent width but three (pc 2326) jumps to `modexpBig` (219). -/
def oneWidth : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [CycleSubmission.Global.Fast.pushAt 1841 1 219,
   CycleSubmission.Global.Fast.opAt 1842 .JUMP]

/-- `e3go` (pc 2329): the E3 hit, square count `1`, jump to the loop head.  Entered by the shift
cleanup tail after the E3 phase switch. -/
def threeHit : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [CycleSubmission.Global.Fast.opAt 1843 .JUMPDEST,
   CycleSubmission.Global.Fast.pushAt 1844 1 1,
   CycleSubmission.Global.Fast.pushAt 1845 2 2369,
   CycleSubmission.Global.Fast.opAt 1846 .JUMP]

def start : List Located :=
  []

/-- Loop head: put the remaining square count minus one in the kernel frame's
`pdst` slot (the in-kernel loop counts it down) and call `SQUARE(0x840) → 0x200`,
entering the kernel's `common` block with `hd = sq_row` and return address 2519. -/
def squareCall : List Located :=
  [CycleSubmission.Global.Fast.opAt 1867 .JUMPDEST,
   CycleSubmission.Global.Fast.pushAt 1868 2 2519,
   CycleSubmission.Global.Fast.pushAt 1869 1 1,
   CycleSubmission.Global.Fast.opAt 1870 (.Dup ⟨2, by decide⟩),
   CycleSubmission.Global.Fast.opAt 1871 .SUB,
   CycleSubmission.Global.Fast.pushAt 1872 2 512,
   CycleSubmission.Global.Fast.pushAt 1873 2 2112,
   CycleSubmission.Global.Fast.pushAt 1874 2 3728,
   CycleSubmission.Global.Fast.pushAt 1875 2 3181,
   CycleSubmission.Global.Fast.opAt 1876 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2317 = true :=
  CycleSubmission.Global.Binding.jumpDest 1835 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2350 = true :=
  CycleSubmission.Global.Binding.jumpDest 1856 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2369 = true :=
  CycleSubmission.Global.Binding.jumpDest 1867 (by rfl)

/-- `modexpBig` (pc 219), the target of every recogniser miss. -/
theorem jumpDestBail :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 219 = true :=
  CycleSubmission.Global.Binding.jumpDest 146 (by rfl)

/-- `modexpBig` (pc 237), where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 219 = true :=
  CycleSubmission.Global.Binding.jumpDest 146 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3181 = true :=
  CycleSubmission.Global.Binding.jumpDest 2476 (by rfl)


/- `after_sq` (pc 3304): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end CycleSubmission.Global.FixedDirectPaths
