import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 16 (instructions 1908..1942).

`LZ` (pc 2695) is the head of the exponent-byte loop body.  It loads exponent
byte `i` and chooses the mask the inner bit loop starts from: `0x80` for every
byte but the first, and the highest set bit of the byte itself for byte `0`.

The three basic blocks are

* `blk1781` (idx 1908..1792, pc 2695..3071) — the byte load and the `i = 0`
  test;
* `blk1793` (idx 1790..1920, pc 2711..3077) — `PUSH1 128` and the jump back
  into the bit loop;
* `blk1796` (idx 1875..1942, pc 2720..3189) — the fold
  `w ||| w >>> 1 ||| w >>> 2 ||| w >>> 4`, then `>>> 1` and `+ 1`, and the
  jump back. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1908..1792, pc 2695..3071: load exponent byte `i`, test `i = 0`. -/
def blk1781 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 904 .JUMPDEST,
   opAt 905 (.Dup ⟨0, by decide⟩),
   pushAt 906 2 2816,
   opAt 907 .MLOAD,
   opAt 908 .ADD,
   opAt 909 .CALLDATALOAD,
   pushAt 910 0 0,
   opAt 911 .BYTE,
   opAt 912 (.Dup ⟨1, by decide⟩),
   opAt 913 .ISZERO,
   pushAt 914 2 1321,
   opAt 915 .JUMPI]

/-- Instructions 1790..1920, pc 2711..3077: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 916 1 128,
   pushAt 917 2 962,
   opAt 918 .JUMP]

/-- Instructions 1875..1942, pc 2720..3189: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 919 .JUMPDEST,
   opAt 920 (.Dup ⟨0, by decide⟩),
   opAt 921 (.Dup ⟨0, by decide⟩),
   pushAt 922 1 1,
   opAt 923 .SHR,
   opAt 924 .OR,
   opAt 925 (.Dup ⟨0, by decide⟩),
   pushAt 926 1 2,
   opAt 927 .SHR,
   opAt 928 .OR,
   opAt 929 (.Dup ⟨0, by decide⟩),
   pushAt 930 1 4,
   opAt 931 .SHR,
   opAt 932 .OR,
   pushAt 933 1 1,
   opAt 934 .SHR,
   pushAt 935 1 1,
   opAt 936 .ADD,
   pushAt 937 2 2160,
   opAt 938 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
