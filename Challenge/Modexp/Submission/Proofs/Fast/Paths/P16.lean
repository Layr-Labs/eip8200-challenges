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
  [opAt 900 .JUMPDEST,
   opAt 901 (.Dup ⟨0, by decide⟩),
   pushAt 902 2 2816,
   opAt 903 .MLOAD,
   opAt 904 .ADD,
   opAt 905 .CALLDATALOAD,
   pushAt 906 0 0,
   opAt 907 .BYTE,
   opAt 908 (.Dup ⟨1, by decide⟩),
   opAt 909 .ISZERO,
   pushAt 910 2 1321,
   opAt 911 .JUMPI]

/-- Instructions 1790..1920, pc 2711..3077: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 912 1 128,
   pushAt 913 2 962,
   opAt 914 .JUMP]

/-- Instructions 1875..1942, pc 2720..3189: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 915 .JUMPDEST,
   opAt 916 (.Dup ⟨0, by decide⟩),
   opAt 917 (.Dup ⟨0, by decide⟩),
   pushAt 918 1 1,
   opAt 919 .SHR,
   opAt 920 .OR,
   opAt 921 (.Dup ⟨0, by decide⟩),
   pushAt 922 1 2,
   opAt 923 .SHR,
   opAt 924 .OR,
   opAt 925 (.Dup ⟨0, by decide⟩),
   pushAt 926 1 4,
   opAt 927 .SHR,
   opAt 928 .OR,
   pushAt 929 1 1,
   opAt 930 .SHR,
   pushAt 931 1 1,
   opAt 932 .ADD,
   pushAt 933 2 2160,
   opAt 934 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
