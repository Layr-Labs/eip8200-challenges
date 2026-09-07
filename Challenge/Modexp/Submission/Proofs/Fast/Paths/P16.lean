import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1812..1846).

`LZ` (pc 2966) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1812..1823, pc 2966..2981) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1824..1826, pc 2982..2987) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1827..1846, pc 2988..3014) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Original block `1781`, now instructions 1812..1823, pc 2966..2981: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1812 .JUMPDEST,
   opAt 1813 (.Dup ⟨0, by decide⟩),
   pushAt 1814 2 9472,
   opAt 1815 .MLOAD,
   opAt 1816 .ADD,
   opAt 1817 .CALLDATALOAD,
   pushAt 1818 0 0,
   opAt 1819 .BYTE,
   opAt 1820 (.Dup ⟨1, by decide⟩),
   opAt 1821 .ISZERO,
   pushAt 1822 2 2988,
   opAt 1823 .JUMPI]

/-- Original block `1793`, now instructions 1824..1826, pc 2982..2987: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1824 1 128,
   pushAt 1825 2 1789,
   opAt 1826 .JUMP]

/-- Original block `1796`, now instructions 1827..1846, pc 2988..3014: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1827 .JUMPDEST,
   opAt 1828 (.Dup ⟨0, by decide⟩),
   opAt 1829 (.Dup ⟨0, by decide⟩),
   pushAt 1830 1 1,
   opAt 1831 .SHR,
   opAt 1832 .OR,
   opAt 1833 (.Dup ⟨0, by decide⟩),
   pushAt 1834 1 2,
   opAt 1835 .SHR,
   opAt 1836 .OR,
   opAt 1837 (.Dup ⟨0, by decide⟩),
   pushAt 1838 1 4,
   opAt 1839 .SHR,
   opAt 1840 .OR,
   pushAt 1841 1 1,
   opAt 1842 .SHR,
   pushAt 1843 1 1,
   opAt 1844 .ADD,
   pushAt 1845 2 3909,
   opAt 1846 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
