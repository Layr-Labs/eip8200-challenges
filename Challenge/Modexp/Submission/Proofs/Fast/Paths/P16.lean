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
  [opAt 1755 .JUMPDEST,
   opAt 1756 (.Dup ⟨0, by decide⟩),
   pushAt 1757 2 9472,
   opAt 1758 .MLOAD,
   opAt 1759 .ADD,
   opAt 1760 .CALLDATALOAD,
   pushAt 1761 0 0,
   opAt 1762 .BYTE,
   opAt 1763 (.Dup ⟨1, by decide⟩),
   opAt 1764 .ISZERO,
   pushAt 1765 2 2906,
   opAt 1766 .JUMPI]

/-- Instructions 1793..1795, pc 2938..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1767 1 128,
   pushAt 1768 2 1765,
   opAt 1769 .JUMP]

/-- Instructions 1796..1815, pc 2944..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1770 .JUMPDEST,
   opAt 1771 (.Dup ⟨0, by decide⟩),
   opAt 1772 (.Dup ⟨0, by decide⟩),
   pushAt 1773 1 1,
   opAt 1774 .SHR,
   opAt 1775 .OR,
   opAt 1776 (.Dup ⟨0, by decide⟩),
   pushAt 1777 1 2,
   opAt 1778 .SHR,
   opAt 1779 .OR,
   opAt 1780 (.Dup ⟨0, by decide⟩),
   pushAt 1781 1 4,
   opAt 1782 .SHR,
   opAt 1783 .OR,
   pushAt 1784 1 1,
   opAt 1785 .SHR,
   pushAt 1786 1 1,
   opAt 1787 .ADD,
   pushAt 1788 2 3827,
   opAt 1789 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
