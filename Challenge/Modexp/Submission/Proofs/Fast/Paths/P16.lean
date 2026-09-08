import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1781..1815).

`LZ` (pc 2922) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1781..1792, pc 2922..2937) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1793..1795, pc 2938..2943) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1796..1815, pc 2944..2970) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1781..1792, pc 2922..2937: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1744 .JUMPDEST,
   opAt 1745 (.Dup ⟨0, by decide⟩),
   pushAt 1746 2 9472,
   opAt 1747 .MLOAD,
   opAt 1748 .ADD,
   opAt 1749 .CALLDATALOAD,
   pushAt 1750 0 0,
   opAt 1751 .BYTE,
   opAt 1752 (.Dup ⟨1, by decide⟩),
   opAt 1753 .ISZERO,
   pushAt 1754 2 2793,
   opAt 1755 .JUMPI]

/-- Instructions 1793..1795, pc 2938..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1756 1 128,
   pushAt 1757 2 1758,
   opAt 1758 .JUMP]

/-- Instructions 1796..1815, pc 2944..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1759 .JUMPDEST,
   opAt 1760 (.Dup ⟨0, by decide⟩),
   opAt 1761 (.Dup ⟨0, by decide⟩),
   pushAt 1762 1 1,
   opAt 1763 .SHR,
   opAt 1764 .OR,
   opAt 1765 (.Dup ⟨0, by decide⟩),
   pushAt 1766 1 2,
   opAt 1767 .SHR,
   opAt 1768 .OR,
   opAt 1769 (.Dup ⟨0, by decide⟩),
   pushAt 1770 1 4,
   opAt 1771 .SHR,
   opAt 1772 .OR,
   pushAt 1773 1 1,
   opAt 1774 .SHR,
   pushAt 1775 1 1,
   opAt 1776 .ADD,
   pushAt 1777 2 3713,
   opAt 1778 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
