import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1781..1815).

`LZ` (pc 2560) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1781..1792, pc 2560..2937) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1793..1795, pc 2576..2943) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1796..1815, pc 2582..2970) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1781..1792, pc 2560..2937: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1739 .JUMPDEST,
   opAt 1740 (.Dup ⟨0, by decide⟩),
   pushAt 1741 2 9472,
   opAt 1742 .MLOAD,
   opAt 1743 .ADD,
   opAt 1744 .CALLDATALOAD,
   pushAt 1745 0 0,
   opAt 1746 .BYTE,
   opAt 1747 (.Dup ⟨1, by decide⟩),
   opAt 1748 .ISZERO,
   pushAt 1749 2 2548,
   opAt 1750 .JUMPI]

/-- Instructions 1793..1795, pc 2576..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1751 1 128,
   pushAt 1752 2 1770,
   opAt 1753 .JUMP]

/-- Instructions 1796..1815, pc 2582..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1754 .JUMPDEST,
   opAt 1755 (.Dup ⟨0, by decide⟩),
   opAt 1756 (.Dup ⟨0, by decide⟩),
   pushAt 1757 1 1,
   opAt 1758 .SHR,
   opAt 1759 .OR,
   opAt 1760 (.Dup ⟨0, by decide⟩),
   pushAt 1761 1 2,
   opAt 1762 .SHR,
   opAt 1763 .OR,
   opAt 1764 (.Dup ⟨0, by decide⟩),
   pushAt 1765 1 4,
   opAt 1766 .SHR,
   opAt 1767 .OR,
   pushAt 1768 1 1,
   opAt 1769 .SHR,
   pushAt 1770 1 1,
   opAt 1771 .ADD,
   pushAt 1772 2 3591,
   opAt 1773 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
