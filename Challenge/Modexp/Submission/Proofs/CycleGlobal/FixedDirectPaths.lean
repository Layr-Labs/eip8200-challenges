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

@[simp] theorem directPC0 (i : Nat) (hi : 1813 ≤ i) (hii : i ≤ 1844) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2284, 2285, 2286, 2288, 2289, 2292, 2293, 2295, 2296, 2297, 2299, 2302, 2303, 2304, 2306, 2307, 2308, 2309, 2312, 2313, 2316, 2317, 2318, 2321, 2322, 2323, 2325, 2326, 2330, 2331, 2333, 2334] : List Nat)[i - 1813]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 1845 ≤ i) (hii : i ≤ 1854) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2336, 2337, 2340, 2342, 2343, 2344, 2347, 2350, 2353, 2356] : List Nat)[i - 1845]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [CycleSubmission.Global.Fast.opAt 1834 .JUMPDEST,
   CycleSubmission.Global.Fast.pushAt 1835 2 2656,
   CycleSubmission.Global.Fast.opAt 1836 .MLOAD,
   CycleSubmission.Global.Fast.opAt 1837 .CALLDATALOAD,
   CycleSubmission.Global.Fast.pushAt 1838 1 232,
   CycleSubmission.Global.Fast.opAt 1839 .SHR,
   CycleSubmission.Global.Fast.pushAt 1840 3 65537,
   CycleSubmission.Global.Fast.opAt 1841 .XOR,
   CycleSubmission.Global.Fast.pushAt 1842 1 207,
   CycleSubmission.Global.Fast.opAt 1843 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [CycleSubmission.Global.Fast.opAt 1813 .JUMPDEST,
   CycleSubmission.Global.Fast.opAt 1814 (.Dup ⟨3, by decide⟩),
   CycleSubmission.Global.Fast.pushAt 1815 1 3,
   CycleSubmission.Global.Fast.opAt 1816 .EQ,
   CycleSubmission.Global.Fast.pushAt 1817 2 2317,
   CycleSubmission.Global.Fast.opAt 1818 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [CycleSubmission.Global.Fast.pushAt 1844 1 16]

/-- Every exponent width but three (pc 2326) jumps to `modexpBig` (219). -/
def oneWidth : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [CycleSubmission.Global.Fast.pushAt 1819 1 207,
   CycleSubmission.Global.Fast.opAt 1820 .JUMP]

/-- `e3go` (pc 2329): the E3 hit, square count `1`, jump to the loop head.  Entered by the shift
cleanup tail after the E3 phase switch. -/
def threeHit : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [CycleSubmission.Global.Fast.opAt 1821 .JUMPDEST,
   CycleSubmission.Global.Fast.pushAt 1822 1 1,
   CycleSubmission.Global.Fast.pushAt 1823 2 2336,
   CycleSubmission.Global.Fast.opAt 1824 .JUMP]

def start : List Located :=
  []

/-- Loop head: put the remaining square count minus one in the kernel frame's
`pdst` slot (the in-kernel loop counts it down) and call `SQUARE(0x840) → 0x200`,
entering the kernel's `common` block with `hd = sq_row` and return address 2519. -/
def squareCall : List Located :=
  [CycleSubmission.Global.Fast.opAt 1845 .JUMPDEST,
   CycleSubmission.Global.Fast.pushAt 1846 2 2519,
   CycleSubmission.Global.Fast.pushAt 1847 1 1,
   CycleSubmission.Global.Fast.opAt 1848 (.Dup ⟨2, by decide⟩),
   CycleSubmission.Global.Fast.opAt 1849 .SUB,
   CycleSubmission.Global.Fast.pushAt 1850 2 512,
   CycleSubmission.Global.Fast.pushAt 1851 2 2112,
   CycleSubmission.Global.Fast.pushAt 1852 2 3710,
   CycleSubmission.Global.Fast.pushAt 1853 2 3146,
   CycleSubmission.Global.Fast.opAt 1854 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2284 = true :=
  CycleSubmission.Global.Binding.jumpDest 1813 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2317 = true :=
  CycleSubmission.Global.Binding.jumpDest 1834 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2336 = true :=
  CycleSubmission.Global.Binding.jumpDest 1845 (by rfl)

/-- `modexpBig` (pc 219), the target of every recogniser miss. -/
theorem jumpDestBail :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 135 (by rfl)

/-- `modexpBig` (pc 237), where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 135 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3146 = true :=
  CycleSubmission.Global.Binding.jumpDest 2405 (by rfl)


/- `after_sq` (pc 3304): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end CycleSubmission.Global.FixedDirectPaths
