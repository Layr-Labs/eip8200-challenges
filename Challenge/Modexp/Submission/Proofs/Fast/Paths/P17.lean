import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 17 (instructions 1823..1863).

`R1C` (pc 2995) stands between the `R1B` top-bit test and `DOUBLE256`.  It is
entered with the stack `[px, ret]` — the calling convention of `DOUBLE256`,
which the `R1B` fall-through now targets here — and handles the two-limb
small-top family directly: when the frame word at `V_S32` says the modulus
has exactly two limbs, its most significant limb is one and its least
significant limb is below 256, `R = radix ^ 2` satisfies `R mod m = lo ^ 2`.
The block stores zero at `px` and `lo ^ 2` at `px + 32` and returns.  Every
other modulus falls through to `DOUBLE256` unchanged.

The four basic blocks are

* `blk1823` (idx 1823..1830, pc 2995..3007) — `JUMPDEST`, the
  `MLOAD V_S32; PUSH1 64; EQ; ISZERO` size test and the `JUMPI` to
  `DOUBLE256` unless the modulus is exactly two limbs;
* `blk1831pass` (idx 1831..1837, pc 3008..3017) — `JUMPDEST`, the
  `MLOAD 0; PUSH1 1; EQ` top-limb test and the taken `JUMPI` to `blk1840`;
* `blk1831bail` (idx 1831..1839, pc 3008..3021) — the same prefix with the
  untaken `JUMPI`, `PUSH2 1911` and the tail jump into `DOUBLE256`;
* `blk1840pass` (idx 1840..1846, pc 3022..3033) — `JUMPDEST`, the
  `MLOAD 32; PUSH2 256; GT` low-limb test and the taken `JUMPI` to `blk1849`;
* `blk1840bail` (idx 1840..1848, pc 3022..3037) — the same prefix with the
  untaken `JUMPI`, `PUSH2 1911` and the tail jump into `DOUBLE256`;
* `blk1849` (idx 1849..1863, pc 3038..3055) — `JUMPDEST`, `MLOAD 32; DUP1;
  MUL` for `lo ^ 2`, the address arithmetic for `px + 32`, zero into `px`,
  `lo ^ 2` into `px + 32`, and the return jump.

All three tests leave the incoming stack `[px, ret]` in place on the
fall-through edges, so every `DOUBLE256` entry sees exactly the frame it
expects. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1823..1830, pc 2995..3007: the two-limb test.  Taken to
`DOUBLE256` unless `V_S32` holds 64. -/
def blk1823 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1823 .JUMPDEST,
   pushAt 1824 2 9344,
   opAt 1825 .MLOAD,
   pushAt 1826 1 64,
   opAt 1827 .EQ,
   opAt 1828 .ISZERO,
   pushAt 1829 2 1911,
   opAt 1830 .JUMPI]

/-- Instructions 1831..1837, pc 3008..3017: the `top = 1` prefix with the
taken `JUMPI` to `blk1840`. -/
def blk1831pass :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1831 .JUMPDEST,
   pushAt 1832 0 0,
   opAt 1833 .MLOAD,
   pushAt 1834 1 1,
   opAt 1835 .EQ,
   pushAt 1836 2 3022,
   opAt 1837 .JUMPI]

/-- Instructions 1831..1839, pc 3008..3021: the same prefix with the untaken
`JUMPI` and the tail jump into `DOUBLE256`. -/
def blk1831bail :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1831 .JUMPDEST,
   pushAt 1832 0 0,
   opAt 1833 .MLOAD,
   pushAt 1834 1 1,
   opAt 1835 .EQ,
   pushAt 1836 2 3022,
   opAt 1837 .JUMPI,
   pushAt 1838 2 1911,
   opAt 1839 .JUMP]

/-- Instructions 1840..1846, pc 3022..3033: the `lo < 256` prefix with the
taken `JUMPI` to `blk1849`. -/
def blk1840pass :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1840 .JUMPDEST,
   pushAt 1841 1 32,
   opAt 1842 .MLOAD,
   pushAt 1843 2 256,
   opAt 1844 .GT,
   pushAt 1845 2 3038,
   opAt 1846 .JUMPI]

/-- Instructions 1840..1848, pc 3022..3037: the same prefix with the untaken
`JUMPI` and the tail jump into `DOUBLE256`. -/
def blk1840bail :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1840 .JUMPDEST,
   pushAt 1841 1 32,
   opAt 1842 .MLOAD,
   pushAt 1843 2 256,
   opAt 1844 .GT,
   pushAt 1845 2 3038,
   opAt 1846 .JUMPI,
   pushAt 1847 2 1911,
   opAt 1848 .JUMP]

/-- Instructions 1849..1863, pc 3038..3055: `lo ^ 2` and `px + 32`, zero into
`px`, `lo ^ 2` into `px + 32`, and the return jump. -/
def blk1849 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1849 .JUMPDEST,
   pushAt 1850 1 32,
   opAt 1851 .MLOAD,
   opAt 1852 (.Dup ⟨0, by decide⟩),
   opAt 1853 .MUL,
   opAt 1854 (.Swap ⟨0, by decide⟩),
   opAt 1855 (.Dup ⟨0, by decide⟩),
   pushAt 1856 1 32,
   opAt 1857 .ADD,
   opAt 1858 (.Swap ⟨0, by decide⟩),
   pushAt 1859 1 0,
   opAt 1860 (.Swap ⟨0, by decide⟩),
   opAt 1861 .MSTORE,
   opAt 1862 .MSTORE,
   opAt 1863 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
