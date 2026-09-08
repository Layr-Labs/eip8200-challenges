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
  [opAt 2029 .JUMPDEST,
   opAt 2030 (.Dup ⟨0, by decide⟩),
   pushAt 2031 2 9472,
   opAt 2032 .MLOAD,
   opAt 2033 .ADD,
   opAt 2034 .CALLDATALOAD,
   pushAt 2035 0 0,
   opAt 2036 .BYTE,
   opAt 2037 (.Dup ⟨1, by decide⟩),
   opAt 2038 .ISZERO,
   pushAt 2039 2 2957,
   opAt 2040 .JUMPI]

/-- Instructions 1793..1795, pc 2938..2943: every byte after the first. -/
def blk1793 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2041 1 128,
   pushAt 2042 2 1789,
   opAt 2043 .JUMP]

/-- Instructions 1796..1815, pc 2944..2970: the highest set bit of byte `0`. -/
def blk1796 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2044 .JUMPDEST,
   opAt 2045 (.Dup ⟨0, by decide⟩),
   opAt 2046 (.Dup ⟨0, by decide⟩),
   pushAt 2047 1 1,
   opAt 2048 .SHR,
   opAt 2049 .OR,
   opAt 2050 (.Dup ⟨0, by decide⟩),
   pushAt 2051 1 2,
   opAt 2052 .SHR,
   opAt 2053 .OR,
   opAt 2054 (.Dup ⟨0, by decide⟩),
   pushAt 2055 1 4,
   opAt 2056 .SHR,
   opAt 2057 .OR,
   pushAt 2058 1 1,
   opAt 2059 .SHR,
   pushAt 2060 1 1,
   opAt 2061 .ADD,
   pushAt 2062 2 3878,
   opAt 2063 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
