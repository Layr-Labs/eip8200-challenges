import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1806..1840).

`LZ` (pc 2951) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1806..1817, pc 2951..2966) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1818..1820, pc 2967..2972) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1821..1840, pc 2973..2999) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Original block `1781`, now instructions 1806..1817, pc 2951..2966: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1806 .JUMPDEST,
   opAt 1807 (.Dup ⟨0, by decide⟩),
   pushAt 1808 2 9472,
   opAt 1809 .MLOAD,
   opAt 1810 .ADD,
   opAt 1811 .CALLDATALOAD,
   pushAt 1812 0 0,
   opAt 1813 .BYTE,
   opAt 1814 (.Dup ⟨1, by decide⟩),
   opAt 1815 .ISZERO,
   pushAt 1816 2 2973,
   opAt 1817 .JUMPI]

/-- Original block `1793`, now instructions 1818..1820, pc 2967..2972: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1818 1 128,
   pushAt 1819 2 1789,
   opAt 1820 .JUMP]

/-- Original block `1796`, now instructions 1821..1840, pc 2973..2999: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1821 .JUMPDEST,
   opAt 1822 (.Dup ⟨0, by decide⟩),
   opAt 1823 (.Dup ⟨0, by decide⟩),
   pushAt 1824 1 1,
   opAt 1825 .SHR,
   opAt 1826 .OR,
   opAt 1827 (.Dup ⟨0, by decide⟩),
   pushAt 1828 1 2,
   opAt 1829 .SHR,
   opAt 1830 .OR,
   opAt 1831 (.Dup ⟨0, by decide⟩),
   pushAt 1832 1 4,
   opAt 1833 .SHR,
   opAt 1834 .OR,
   pushAt 1835 1 1,
   opAt 1836 .SHR,
   pushAt 1837 1 1,
   opAt 1838 .ADD,
   pushAt 1839 2 3894,
   opAt 1840 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
