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
  [opAt 1709 .JUMPDEST,
   opAt 1710 (.Dup ⟨0, by decide⟩),
   pushAt 1711 2 9472,
   opAt 1712 .MLOAD,
   opAt 1713 .ADD,
   opAt 1714 .CALLDATALOAD,
   pushAt 1715 0 0,
   opAt 1716 .BYTE,
   opAt 1717 (.Dup ⟨1, by decide⟩),
   opAt 1718 .ISZERO,
   pushAt 1719 2 2365,
   opAt 1720 .JUMPI]

/-- Instructions 1793..1795, pc 2576..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1721 1 128,
   pushAt 1722 2 1715,
   opAt 1723 .JUMP]

/-- Instructions 1796..1815, pc 2582..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1724 .JUMPDEST,
   opAt 1725 (.Dup ⟨0, by decide⟩),
   opAt 1726 (.Dup ⟨0, by decide⟩),
   pushAt 1727 1 1,
   opAt 1728 .SHR,
   opAt 1729 .OR,
   opAt 1730 (.Dup ⟨0, by decide⟩),
   pushAt 1731 1 2,
   opAt 1732 .SHR,
   opAt 1733 .OR,
   opAt 1734 (.Dup ⟨0, by decide⟩),
   pushAt 1735 1 4,
   opAt 1736 .SHR,
   opAt 1737 .OR,
   pushAt 1738 1 1,
   opAt 1739 .SHR,
   pushAt 1740 1 1,
   opAt 1741 .ADD,
   pushAt 1742 2 3385,
   opAt 1743 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
