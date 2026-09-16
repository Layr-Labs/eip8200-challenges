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

@[simp] theorem directPC0 (i : Nat) (hi : 1635 ≤ i) (hii : i ≤ 1668) :
    Artifact.submissionArtifact.instructionPC i =
      ([2182,2183,2184,2186,2187,2190,2191,2192,2194,2195,2198,2199,2202,2203,2204,2205,2206,2208,2209,2212,2213,2215,2218,2219,2220,2223,2224,2225,2227,2228,2232,2233,2236,2237] : List Nat)[i - 1635]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem directPC1 (i : Nat) (hi : 1669 ≤ i) (hii : i ≤ 1701) :
    Artifact.submissionArtifact.instructionPC i =
      ([2239,2240,2241,2244,2245,2248,2251,2252,2253,2256,2259,2260,2261,2262,2263,2264,2265,2268,2269,2270,2273,2276,2277,2280,2283,2284,2285,2286,2289,2292,2293,2294,2297] : List Nat)[i - 1669]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

def check65537 : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1658 .JUMPDEST,
   pushAt 1659 2 2816,
   opAt 1660 .MLOAD,
   opAt 1661 .CALLDATALOAD,
   pushAt 1662 1 232,
   opAt 1663 .SHR,
   pushAt 1664 3 65537,
   opAt 1665 .XOR,
   pushAt 1666 2 2284,
   opAt 1667 .JUMPI]

def checkThree : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1646 2 2816,
   opAt 1647 .MLOAD,
   opAt 1648 .CALLDATALOAD,
   pushAt 1649 0 0,
   opAt 1650 .BYTE,
   pushAt 1651 1 3,
   opAt 1652 .XOR,
   pushAt 1653 2 2284,
   opAt 1654 .JUMPI]

def entryPrefix : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1635 .JUMPDEST,
   opAt 1636 (.Dup ⟨3, by decide⟩),
   pushAt 1637 1 3,
   opAt 1638 .EQ,
   pushAt 1639 2 2219,
   opAt 1640 .JUMPI]

def fermatHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1668 1 16]

def oneWidth : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1641 (.Dup ⟨3, by decide⟩),
   pushAt 1642 1 1,
   opAt 1643 .XOR,
   pushAt 1644 2 2284,
   opAt 1645 .JUMPI]

def threeHit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1655 1 1,
   pushAt 1656 2 2239,
   opAt 1657 .JUMP]

def start : List Located :=
  []

/-- Loop head: store the remaining square count at `0x2440` (read by the
kernel's in-kernel loop) and call `SQUARE(0x800) → 0x800`, entering the kernel's
`common` block with `hd = sq_row` and return address 3292. -/
def squareCall : List Located :=
  [opAt 1669 .JUMPDEST,
   opAt 1670 (.Dup ⟨0, by decide⟩),
   pushAt 1671 2 2624,
   opAt 1672 .MSTORE,
   pushAt 1673 2 2260,
   pushAt 1674 2 512,
   opAt 1675 (.Dup ⟨0, by decide⟩),
   opAt 1676 (.Dup ⟨0, by decide⟩),
   pushAt 1677 2 4394,
   pushAt 1678 2 3213,
   opAt 1679 .JUMP]

def squareReturn : List Located :=
  [opAt 1680 .JUMPDEST,
   pushAt 1681 0 0,
   opAt 1682 .NOT,
   opAt 1683 .ADD,
   opAt 1684 (.Dup ⟨0, by decide⟩),
   pushAt 1685 2 2239,
   opAt 1686 .JUMPI]

/-- `after_sq` (pc 3304): both the in-kernel loop's return target and the
fall-through of the caller loop for the unaccelerated widths.  The square count
left on the stack is dropped and the final mixed-domain product is called. -/
def product : List Located :=
  [opAt 1687 .POP,
   pushAt 1688 2 1049,
   pushAt 1689 2 256,
   opAt 1690 (.Dup ⟨0, by decide⟩),
   pushAt 1691 2 512,
   pushAt 1692 2 3209,
   opAt 1693 .JUMP]

def fallback : List Located :=
  [opAt 1694 .JUMPDEST,
   opAt 1695 (.Dup ⟨0, by decide⟩),
   pushAt 1696 2 1024,
   pushAt 1697 2 256,
   opAt 1698 .MCOPY,
   pushAt 1699 0 0,
   pushAt 1700 2 950,
   opAt 1701 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2182 = true :=
  Artifact.isValidJumpDest_index 1635 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2219 = true :=
  Artifact.isValidJumpDest_index 1658 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2239 = true :=
  Artifact.isValidJumpDest_index 1669 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2260 = true :=
  Artifact.isValidJumpDest_index 1680 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2284 = true :=
  Artifact.isValidJumpDest_index 1694 (by rfl)

/-- The kernel's multiply entry `0x0f50` (the final mixed-domain product). -/
theorem jumpDestSqMulEntry :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3209 = true :=
  Artifact.isValidJumpDest_index 2380 (by rfl)

/-- The kernel's shared `common` block `0x0f54` (entered by the square call). -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3213 = true :=
  Artifact.isValidJumpDest_index 2382 (by rfl)


/- `after_sq` (pc 3304): the target the in-kernel square loop rewrites the
kernel frame's return slot to. -/

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
