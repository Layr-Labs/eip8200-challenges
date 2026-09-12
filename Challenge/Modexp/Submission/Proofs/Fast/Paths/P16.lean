import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1911..1945).

`LZ` (pc 2698) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1911..1792, pc 2698..3074) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1793..1925, pc 2714..3080) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1878..1945, pc 2720..3107) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1911..1792, pc 2698..3074: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1638 .JUMPDEST,
   opAt 1639 (.Dup ⟨0, by decide⟩),
   pushAt 1640 2 5376,
   opAt 1641 .MLOAD,
   opAt 1642 .ADD,
   opAt 1643 .CALLDATALOAD,
   pushAt 1644 0 0,
   opAt 1645 .BYTE,
   opAt 1646 (.Dup ⟨1, by decide⟩),
   opAt 1647 .ISZERO,
   pushAt 1648 2 2254,
   opAt 1649 .JUMPI]

/-- Instructions 1793..1925, pc 2714..3080: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1650 1 128,
   pushAt 1651 2 1616,
   opAt 1652 .JUMP]

/-- Instructions 1878..1945, pc 2720..3107: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1653 .JUMPDEST,
   opAt 1654 (.Dup ⟨0, by decide⟩),
   opAt 1655 (.Dup ⟨0, by decide⟩),
   pushAt 1656 1 1,
   opAt 1657 .SHR,
   opAt 1658 .OR,
   opAt 1659 (.Dup ⟨0, by decide⟩),
   pushAt 1660 1 2,
   opAt 1661 .SHR,
   opAt 1662 .OR,
   opAt 1663 (.Dup ⟨0, by decide⟩),
   pushAt 1664 1 4,
   opAt 1665 .SHR,
   opAt 1666 .OR,
   pushAt 1667 1 1,
   opAt 1668 .SHR,
   pushAt 1669 1 1,
   opAt 1670 .ADD,
   pushAt 1671 2 3248,
   opAt 1672 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
