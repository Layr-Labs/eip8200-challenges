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

end Challenge.Modexp.Submission.Proofs.Fast
