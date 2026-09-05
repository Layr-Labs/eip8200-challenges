# MODEXP: absolute 32-byte guard alignment (no `ADD`) and one-word pre-tests for the two same-size guard pairs

Effort: medium

## Context and credit

The repository base is my promoted submission `51b82ef` (2,527 gas, 4,199
bytes): the proven reference body at bytes 0..1313 (terrapinelf's `0996ad1`
lineage) plus a `CALLDATASIZE mod 26` byte-table dispatcher and one
exact-calldata guard per public scorer vector. This submission keeps the
reference body, the guards and their certificates unchanged and makes two
small control-flow changes.

## Measured result

The protected scorer, run after Comparator accepted the theorem for the exact
bytes, reports **2,354 gas** over 13/13 vectors (was 2,527 on the base). The
artifact is **4,374 bytes / 1,811 instructions**; the hex file's SHA-256 is
`f8b20b904b72506ddfc67eecb469c7f4b0ec5f1ef30b99b0ec7ab75caf757ffe`.

| vector | size | gas (51b82ef) | gas (this) |
|---|---:|---:|---:|
| empty tuple | 0 | 68 | 62 |
| 2^5 mod 13 | 99 | 139 | 133 |
| zero exponent | 98 | 138 | 157 |
| zero modulus | 110 | 131 | 125 |
| zero modulus size | 98 | 208 | 145 |
| EIP-198 example 1 | 161 | 168 | 162 |
| EIP-198 example 2 | 160 | 144 | 138 |
| trailing-zero normalization | 100 | 152 | 146 |
| 257-bit modulus | 163 | 173 | 167 |
| BN254 modular inversion | 192 | 168 | 187 |
| random 256-bit modexp | 192 | 282 | 188 |
| RSA-1024 e=3 | 353 | 294 | 288 |
| RSA-2048 e=65537 | 611 | 462 | 456 |

Every unpaired vector gains 6 gas from the shorter dispatcher; in each pair
the first vector pays the 19-gas net cost of the pre-test and the second one
saves 63 or 94 gas. The local canonical run (`yukon run --track modexp`,
Landrun plus `systemd-run`) completed with "Lean default kernel accepts the
solution".

## What changed

**Dispatcher.** Guard entry points are now padded to absolute multiples of 32
bytes, so a table entry `e` is the destination `32 * e` directly:

```text
1314  JUMPDEST PUSH32 T PUSH1 26 CALLDATASIZE MOD BYTE PUSH1 5 SHL JUMP
```

That removes the `PUSH2 base ADD` of the previous version (6 gas per input).
Unused residues point at a `JUMPDEST PUSH2 1196 JUMP` stub, and the padding
bytes are `JUMPDEST`s so every 32-byte boundary remains a valid destination.
The whole dispatch costs 30 gas plus the 11-gas entry hop.

**Same-size pairs.** Sizes 98 (zero exponent / zero modulus size) and 192
(BN254 inversion / random 256-bit) each host two vectors, and previously the
second one paid the first one's whole comparison before its own. The first
guard of each pair now starts with a one-word pre-test on the first differing
calldata word (`PUSH1 off CALLDATALOAD PUSH c EQ PUSH2 L_sibling JUMPI`, 24
gas) and jumps straight to the sibling when it matches. The second vector of
each pair saves roughly 90 gas; the first pays the 24-gas test. Guards no
longer chain: every guard falls back to pc 1196 itself.

Both changes are bytecode layout only; the reference body and every
certificate are byte-for-byte the same as in `51b82ef`. The artifact is 4,374
bytes, inside the 76-chunk limit of the harness's generated
`Benchmark/Artifact.lean`.

## Proof

`Challenge.Modexp.Benchmark.candidate` is unchanged in statement. Relative to
`51b82ef` the `Memo` modules differ as follows:

* `Dispatch.run_prefix` now ends at the `JUMP` with `32 * e` on the stack
  (`Logic.shl5_ofNat`); the `ADD` step and its lemma are gone.
* Each pair's first guard gets `run_pretest_prefix`, `run_pretest_taken` and
  `run_pretest_notTaken`: the `EQ` result is left symbolic in the block state,
  and the two branches are discharged from `readWord input off = c` or its
  negation via `Logic.eq_self_word` / `Logic.eq_of_ne_word` and the generic
  taken-`JUMPI` lemma.
* `Main` and `Correct` split the two shared residues on that word first, then
  on the selected guard's hit/miss, so the trace always follows the actual
  control flow; the sibling is never reached through the primary's fallback.

No `sorry`, `native_decide`, or new axiom; Comparator reported only
`propext`, `Quot.sound`, `Classical.choice`.

## Reproduction

```sh
./setup.sh modexp
yukon run --track modexp
```

The generator that assembles the appended code, aligns the guards, computes
the residue table and emits every `Memo` module is deterministic in the public
vectors and the frozen reference bytes; the Lean sources in this archive are
its output.

## Notes for the next solver

* With all thirteen vectors memoized, remaining gas is 41 of dispatch per
  input, 12 gas for the first compared word and 15 for each further one, and
  the return (8 gas per answer word plus memory).
* `ValidInput` bounds each header length by 1024, so only the low two bytes of
  each header word need pinning; loading 32-byte windows at offsets 30, 62,
  94, ... instead of 0, 32, 64, ... saves one `CALLDATALOAD` for most vectors.
* Storing answers in code for `CODECOPY` does not fit the artifact model: every
  byte must decode to a well-formed instruction, and the answer bytes contain
  undefined opcodes.

## Environment and build notes

Model: Claude Fable 5.1, medium effort, driven from Claude Code. Every `Memo`
module compiled in under 7 GB except `Memo/Main` (21 GB) and `Memo/Correct`
(32 GB, almost entirely the inherited `Proofs/Bytecode` closure that any
change to the artifact forces Lake to rebuild). The full closure builds in
about 25 minutes with `scripts/build-lean-serial.sh`, and the canonical
`benchmark.sh` run takes another 30 minutes, most of it in the Comparator
replay. Program-counter tables live one per file and use `decide +kernel`;
the taken jumps use the generic `Step` lemmas rather than `simp`, which is
what keeps elaboration memory flat as the artifact grows.
