import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1906..1940).

`LZ` (pc 2693) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1906..1792, pc 2693..3069) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1788..1920, pc 2709..3075) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1873..1940, pc 2720..3102) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1906..1792, pc 2693..3069: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1635 .JUMPDEST,
   opAt 1636 (.Dup ⟨0, by decide⟩),
   pushAt 1637 2 2816,
   opAt 1638 .MLOAD,
   opAt 1639 .ADD,
   opAt 1640 .CALLDATALOAD,
   pushAt 1641 0 0,
   opAt 1642 .BYTE,
   opAt 1643 (.Dup ⟨1, by decide⟩),
   opAt 1644 .ISZERO,
   pushAt 1645 2 2249,
   opAt 1646 .JUMPI]

/-- Instructions 1788..1920, pc 2709..3075: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1647 1 128,
   pushAt 1648 2 1611,
   opAt 1649 .JUMP]

/-- Instructions 1873..1940, pc 2720..3102: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1650 .JUMPDEST,
   opAt 1651 (.Dup ⟨0, by decide⟩),
   opAt 1652 (.Dup ⟨0, by decide⟩),
   pushAt 1653 1 1,
   opAt 1654 .SHR,
   opAt 1655 .OR,
   opAt 1656 (.Dup ⟨0, by decide⟩),
   pushAt 1657 1 2,
   opAt 1658 .SHR,
   opAt 1659 .OR,
   opAt 1660 (.Dup ⟨0, by decide⟩),
   pushAt 1661 1 4,
   opAt 1662 .SHR,
   opAt 1663 .OR,
   pushAt 1664 1 1,
   opAt 1665 .SHR,
   pushAt 1666 1 1,
   opAt 1667 .ADD,
   pushAt 1668 2 3243,
   opAt 1669 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
