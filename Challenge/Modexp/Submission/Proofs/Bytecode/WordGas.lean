import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
import Challenge.EvmProof.Meter
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-!
# Gas of the one-word MODEXP path

The path is value-independent: the only input-dependent loop counts are
`bsize / 32` full base words and `esize` exponent bytes.  Nothing inside either
loop expands memory — the base loop touches no memory at all, and every window
`MLOAD` is at `32 * (w / 16)` or `32 * (w mod 16)`, both below `0x200`, with
sixteen words already active (`Word.activeWords_table`).  So both per-iteration
costs are constants.

`wordGasCert` is the honest number: the cost carried by the execution
certificate itself, correct by construction.

`wordGas` is the closed form.  Its constants were obtained by summing the
Osaka base costs of the merged bytes block by block, **not** by proving
`wordGas = wordGasCert`; that equality is not established here.  Treat
`wordGas` as documentation of the cost model and `wordGasCert` as the fact.

Derivation of the constants, per block of the region:

| block | indices | gas |
|---|---|---|
| trampoline | 430–432 | 12 |
| body entry | 1495–1520 | 84 |
| base guard + `JUMPI` | 1521–1527 | 26 |
| base body + back-edge | 1528–1543 | 62 |
| table init (`T[0]`, `T[1]`) | 1544–1555 | 33 |
| table `T[2]` | 1556–1563 | 29 |
| table `T[3] … T[15]` | 1564–1654 | 338 |
| table load + loop setup | 1655–1660 | 15 |
| byte guard + `JUMPI` | 1661–1667 | 26 |
| byte body (2 windows, 8 squarings) | 1668–1729 | 239 |
| byte exit | 1730–1737 | 25 |
| return tail | 536–549 | 36 |

Per base word `26 + 62 = 88`; per exponent byte `26 + 239 = 265`.  The
straight-line remainder, counting each loop's exit test once, is `624`.
Memory expansion is two steps: `0 → 16` words for the window table
(`memCost 16 - memCost 0 = 48`) and `16 → 193` words for the return buffer at
`0x1800` (`memCost 193 - memCost 16 = 603`), so `624 + 651 = 1275`.

Cross-check: the two EIP-198 scored vectors have `bsize = esize = msize = 32`,
giving `1275 + 88 * 1 + 265 * 32 = 9843` for the region; with the header and
dispatch prefix this is the measured 9,964.  The reference path spends
`140` gas per *base byte* and `1210` per exponent byte, which is where the
41,609 → 10,052 field-inversion improvement comes from.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordGas

open EvmSemantics
open EvmSemantics.EVM
open Word
open WordLoops
open WordExit

/-- Gas per full 32-byte word of the base: guard `26` plus body `62`. -/
def baseWordGas : Nat := 88

/-- Gas per exponent byte: guard `26` plus the unrolled two-window body `239`. -/
def expByteGas : Nat := 265

/-- Straight-line gas of the region, including both loop-exit tests, the
window-table construction, and both memory expansions. -/
def wordConstGas : Nat := 1275

/-- Closed form.  See the module docstring: measured, not proved. -/
def wordGas (input : ByteArray) : Nat :=
  wordConstGas + baseWordGas * (baseSize input / 32) +
    expByteGas * exponentSize input

/-- The gas the execution certificate actually carries, from
`Dispatch.wordEntryState` to the `RETURN`.  Correct by construction. -/
def wordGasCert (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodpos : 0 < modulusValue input) : Nat :=
  (gasSteps_wordTotal input hvalid hmsize hword hmodpos).cost

/-- The zero-modulus path never enters the appended body. -/
def zeroModulusGasCert (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : modulusValue input = 0) : Nat :=
  (gasSteps_zeroModulus input hvalid hmsize hword hmodulus).cost

end Challenge.Modexp.Submission.Proofs.Bytecode.WordGas
