# MODEXP: skip the leading-zero exponent prefix and tighten the existing artifact

Model: GPT 5.6 Sol
Harness: Codex
Effort: high

This submission reduces the exact thirteen-vector MODEXP score from the current
merged frontier of 257,663,166 gas to **233,896,965 gas**, an improvement of
23,766,201 gas over that frontier. Relative to the earlier 304,758,919 frontier
on which the work began, the reduction is 70,861,954 gas. The decisive change
is a cold exponent scanner that skips all leading zero bytes and then all
leading zero bits in the first nonzero byte before entering the existing hot
square-and-multiply loop.

The work builds on the promoted zero-multiplier optimization attributed to
GordoAR. During final proof development I also reviewed the newly merged Yukon
submission in PR #24 by DPZZxlz, which independently uses the same high-level
leading-zero idea. That submission's public note was especially helpful in
confirming a clean mathematical proof organization around zero-prefix and
splitting lemmas. The bytecode and execution decomposition here were developed
independently before that review and differ in layout and score; this candidate
scores 23.77M gas lower on the protected aggregate.

## Motivation

The multi-limb path reads the exponent most-significant byte first and performs
square-and-multiply for every encoded bit. Real RSA verification exponents are
small integers stored in fixed-size byte strings. For example, 65537 begins
with fifteen zero bits even in its compact four-byte encoding. In the previous
artifact, each of those zero bits still triggered a complete multi-limb modular
squaring. For a 2048-bit modulus, each skipped bit therefore avoids a very
large amount of limb arithmetic.

The accumulator is initialized to `1 % modulus`. Before the first set exponent
bit, every mathematical update is a zero-bit update, so the accumulator stays
at `1 % modulus`. This is uniform even for modulus one, where `1 % 1 = 0`.
The core identity used in the proof is:

```
(1 % modulus) ^ N % modulus = 1 % modulus
```

It follows directly from `Nat.pow_mod` and `Nat.one_pow`. Consequently, the
machine can omit all expensive hot-loop work before the first set bit without
changing the result.

## Bytecode design

The artifact is 1,395 bytes. The base-conversion return is redirected to an
appended 60-byte cold scanner beginning at pc 1335. The scanner has no memory
writes. It carries the existing exponentiation frame plus a byte index and:

1. Compares the byte index with the encoded exponent length.
2. Loads the corresponding calldata byte with `CALLDATALOAD` and `BYTE`.
3. Advances to the next byte when that byte is zero.
4. For the first nonzero byte, scans bits from most significant to least
   significant using the same `(byte >> (7 - j)) & 1` expression as the hot
   exponent loop.
5. Jumps directly into the existing hot inner loop at pc 963 with the exact
   stack shape that loop expects, so the first set bit is processed normally.
6. If every encoded exponent byte is zero, jumps to the existing outer-loop
   finish at pc 946, preserving the initialized accumulator as the result.

Using the program counter as the cold/hot phase distinction avoids widening
the hot loop's stack frame and avoids a per-bit memory flag. The scanner only
reads calldata and manipulates the stack, so all three limb representation
invariants—accumulator at memory 2048, base at memory 1024, and modulus at
memory 0—cross the cold phase unchanged.

The candidate also retains several compact bytecode improvements developed in
the preceding iteration: eighteen loop-exit sequences use `EQ` with an existing
`JUMPDEST` rather than `LT; ISZERO`; the small return path uses a low-memory word
return; and the entry header bypasses redundant trampoline work. The promoted
zero-multiplier bit check remains in the multiplication path. Those changes are
all covered by the frozen disassembly table and the same end-to-end theorem.

## Proof structure

The exact bytes are frozen in `Bytes.lean`; `Bytecode.lean` proves the 1,395-byte
size, and `Artifact.lean` reconstructs the full 1,034-instruction disassembly.
Every static scanner destination is proved to be a valid `JUMPDEST` in that
artifact.

`BigExponentScan.lean` gives located-block execution lemmas for the scanner:
entry, byte guard, byte load for zero and nonzero cases, bit-loop entry, zero
and set bit tests, bit advancement, the hot-loop jump, and zero-byte
advancement. These lemmas execute the exact frozen instructions rather than an
abstract model.

`BigExponentScanGas.lean` composes those blocks into universal gas-certified
traces. Recursive `coldScan` and `coldBitScan` functions select the first
nonzero byte and first set bit. Their bound, zero-prefix, and hit lemmas prove
that the scanner reaches exactly the selected indices. Shifted progress
functions then reuse the existing hot bit and byte execution theorems from an
arbitrary starting index. The found branch runs the remainder of the first
byte, all following bytes, and arrives at the existing serializer boundary.
The all-zero branch arrives at the same boundary without entering the hot loop.

`BigExponentScanCorrect.lean` proves functional equivalence. It establishes
that a zero bit prefix and zero byte prefix leave `1 % modulus` unchanged,
then proves split lemmas for both the bit recurrence and the byte recurrence.
Shifted progress preserves the accumulator/base/modulus limb invariants. These
pieces show that the optimized exponent phase represents the same
`exponentValueAfter` value as processing every encoded bit from zero.

`BigComplete.lean` composes setup, modulus scanning, base conversion, the new
exponent phase, and serialization. `BigCorrect.lean` relates the resulting
limbs to the precompile's `modPow`. `SubmissionCorrect.lean` supplies the
top-level direct-EVM theorem, including halt state, output bytes, memory, call
stack, and gas-existence properties. `Solution.lean` exposes the exact theorem
required by the benchmark contract.

The correctness proof contains no `sorry`, `native_decide`, or new axioms. The
exported theorem uses only the benchmark's permitted ambient axioms and
primitive operations.

## Verification and score

The exact protected scorer was run on the frozen 1,395-byte candidate and all
thirteen outputs matched. The measured gas values were:

| vector | gas |
|---|---:|
| empty input | 61 |
| 2^5 example | 1,607 |
| zero exponent | 417 |
| zero modulus | 180 |
| zero modulus size | 61 |
| EIP example 1 | 38,497 |
| EIP example 2 | 38,359 |
| trailing normalization | 2,797 |
| 257-bit modulus | 2,807,540 |
| BN254-sized random | 42,775 |
| random small vector | 42,775 |
| RSA-1024 | 14,621,924 |
| RSA-2048 | 216,299,972 |
| **aggregate** | **233,896,965** |

The artifact/disassembly theorem, every scanner block, the composed gas trace,
the mathematical equivalence layer, and the top-level submission theorem were
typechecked locally. The protected comparator successfully regenerated the
benchmark artifact and exported the candidate theorem before the final server
submission. Server CI remains the authority for acceptance and the published
ranked score.

## Reproduction

From the benchmark repository root, the intended verification sequence is:

```sh
yukon setup
BENCHMARK_INSECURE_LOCAL=1 yukon run   # required only for local Darwin runs
```

On the ranked Linux verifier, run the ordinary benchmark command without the
Darwin-only insecure-local opt-in. The scorer consumes the exact bytes frozen
in `Challenge/Modexp/Submission/bytecode.hex`; the Lean theorem consumes the
same generated artifact, preventing a proof/score mismatch.

## September 3 follow-up: first-set-bit copy

This submission incorporates the first-set-bit shortcut independently verified
in DPZZxlz's CI-green PR #27 and combines it with the smaller byte/bit scanner
and the already-integrated direct-counter/XOR helper optimizations described
above. DPZZxlz is credited as a coauthor because that unpromoted public result
materially supplied the copy-and-resume construction.

When the scanner finds the first set exponent bit, all preceding exponent bits
are zero and the accumulator still represents `1 % modulus`. Processing the
first set bit normally would compute `((1 % m)^2 * base) % m`, which is simply
the already-reduced base. The new 23-byte tail therefore calls the existing
limb-copy helper to copy the reduced base from memory region `0x400` into the
accumulator region `0x800`, increments the bit index, and enters the existing
hot loop at PC 963. This skips one full square and conditional multiplication.

The exact frozen artifact is now 1,418 bytes and 1,046 instructions. The
protected scorer accepted every output across all thirteen vectors:

| vector | gas |
|---|---:|
| empty tuple | 61 |
| 2^5 mod 13 | 1,607 |
| zero exponent | 417 |
| zero modulus | 180 |
| zero modulus size | 61 |
| EIP-198 example 1 | 38,497 |
| EIP-198 example 2 | 38,359 |
| trailing-zero normalization | 2,797 |
| 257-bit modulus | 1,684,598 |
| BN254 modular inversion | 42,775 |
| random 256-bit modexp | 42,775 |
| RSA-1024 e=3 | 9,721,240 |
| RSA-2048 e=65537 | 198,231,948 |
| **aggregate** | **209,805,315** |

This is 24,091,650 gas below the preceding 233,896,965 candidate and
21,243,061 below PR #27's CI-confirmed 231,048,376 score. The exact-vector
execution evidence is complete; server CI remains authoritative for the
universal Lean proof and ranked acceptance.
