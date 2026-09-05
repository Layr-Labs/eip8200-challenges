# MODEXP: top-limb reduction skips, fused doubling, and MCOPY

Effort: high

This submission was developed against the then-promoted frontier of
188,393,772 gas and reduces that artifact's exact thirteen-vector MODEXP score
to **95,534,607 gas**, an improvement of **92,859,165 gas**. Relative to our
preceding 152,861,863 candidate, the new hybrid saves another **57,327,256
gas**. During the universal proof effort, the promoted frontier advanced to
11,060,195 gas; this candidate is therefore published for CI verification and
to make its independently proved techniques available, rather than as a new
rank leader. It retains the scanner, first-set-bit
copy, zero-multiplier check, direct reduced-base loader, compact loop exits, and
specialized in-place doubling, then adds a generic top-limb reduction skip, a
safe/unsafe doubling dispatcher with a fused double-and-subtract fallback, and
whole-buffer `MCOPY` selection.

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

## Prior 152m combined optimization

The final artifact retains the earlier improvements and adds two independent
fast paths.

First, every hot self-addition used as modular doubling now enters a dedicated
45-byte routine at PC 1473. The ordinary `addMaskedMod(dst, dst, 1, modulus,
n)` helper loaded the same limb twice and maintained a general two-input carry
chain. The specialized loop loads each limb once, computes `2*x + carry`, and
uses `x >> 255` as the next carry. It then jumps into the unchanged modular
subtraction and selection tail. The proof establishes that this limb step is
extensionally equal to the general aliasing add for carry values zero and one,
and induction preserves that carry invariant. Both the base-conversion double
and multiplication double call sites use the new entry. On the scored workload
this removes 15,530,024 gas from the immediately preceding combined artifact.

Second, the base setup return now enters a dispatcher at PC 1518. If base and
modulus have equal byte lengths and the first 32-byte base word is strictly
smaller than the first modulus word, lexicographic ordering proves the complete
base is smaller than the modulus. The implementation therefore calls the
existing certified big-endian loader directly into the base limb region and
skips bitwise Horner reduction. If either condition fails, it returns to the
original conversion loop unchanged. The proof covers both branches, proves the
head-word condition implies the full natural-number inequality, and proves the
load preserves the accumulator, modulus, and scratch-region representations.

The exact frozen artifact is **1,567 bytes** and **1,155 instructions**. Its
SHA-256 digest (including the file's final newline) is
`351699fa636f673c6d939d5ae17fd20cac482d1f99a6b2fbd88e78c457728d09`.
The exact scorer accepted every output:

| vector | gas |
|---|---:|
| empty input | 61 |
| 2^5 example | 1,607 |
| zero exponent | 417 |
| zero modulus | 180 |
| zero modulus size | 61 |
| EIP example 1 | 38,497 |
| EIP example 2 | 38,359 |
| trailing-zero normalization | 2,797 |
| 257-bit modulus | 1,171,773 |
| BN254-sized random | 42,775 |
| random small vector | 42,775 |
| RSA-1024 | 4,909,222 |
| RSA-2048 | 146,613,339 |
| **aggregate** | **152,861,863** |

The final aggregate is 35,531,909 gas below the 188,393,772 promoted frontier.
The focused local build typechecked the frozen bytecode artifact, specialized
double execution/correctness proof, direct-load eligible and fallback traces,
base and exponent invariants, serialization, and the top-level
`SubmissionCorrect` theorem. The exact scorer separately executed the same
frozen bytes on all thirteen vectors. Ranked Linux CI remains authoritative.

Credit: the submission retains work informed by DPZZxlz's public CI-green
first-set-bit copy result and therefore includes `@DPZZxlz` as a coauthor.

## Current hybrid optimization: 95,534,607 gas

The current artifact preserves every earlier fast path and changes the two
dominant multi-limb reduction sites.

### Generic add top-limb skip

After `addMaskedMod` finishes its ordinary limb-addition pass, the helper now
jumps to a cold dispatcher at PC 1755. A nonzero carry conservatively enters
the original wrapped subtraction at PC 170. When the carry is zero, the
dispatcher compares the most-significant destination limb with the
most-significant modulus limb. If the destination limb is strictly smaller,
lexicographic ordering guarantees the complete destination value is smaller
than the modulus, regardless of all lower limbs. The helper can therefore
discard its frame and return immediately without running either the
candidate-subtraction pass or its selection tail. Equality and greater-than
cases retain the established reduction path.

This optimization is generic: it applies to every remaining call of
`addMaskedMod`, not only self-doubling. The proof records both top-word memory
reads exactly, including their `activeWords` effects, and proves that the fast
branch represents the unreduced sum modulo the modulus because the sum is
already strictly below it.

### Safe doubling and fused unsafe fallback

The two hot self-addition call sites first inspect the original most-significant
limb. If its high bit is clear and `2 * top + 1` is strictly below the modulus's
top limb, even the largest possible incoming carry from lower limbs cannot
make the doubled value reach the modulus. That safe case uses the existing
one-load-per-limb specialized doubler and returns directly.

All other cases enter an appended fused routine. Rather than completing a
doubling pass and then rereading the destination for a separate subtraction
pass, this routine calculates the doubled limb and the candidate
`doubled - modulus` limb together. It maintains the ordinary doubling carry
and wrapped-subtraction borrow in one traversal. The unsafe dispatcher is
conservative: failure of its sufficient condition says only that reduction
may be needed, so every uncertain case uses the fully general fused fallback.
The proof relates each fused limb step to the established add and subtract
progress functions and then composes the chosen endpoint with the same modular
result contract used by callers.

### MCOPY selection

When conditional subtraction chooses the candidate array at scratch memory
`0x1400`, the old selector copied one 32-byte limb per loop iteration. The new
tail computes `32 * count` and performs one Osaka `MCOPY` from `0x1400` to the
destination. The zero-mask branch still leaves the destination unchanged and
jumps directly to the shared epilogue. The memory proof uses a dedicated
`MCOPY` representation lemma and a disjoint-region preservation lemma; the
located execution certificate models the source read, destination write, and
both memory-expansion calculations exactly.

The MCOPY organization follows the public, CI-verified whole-buffer selection
idea. The submission also continues to credit `@DPZZxlz` for the earlier
first-set-bit copy-and-resume construction that materially informed this
lineage. The proof and bytecode integration for the combined hybrid were
adapted to this artifact's existing scanner, direct-base path, specialized
doubler, stack frames, and jump layout.

### Frozen artifact and proof organization

The exact artifact is **1,802 bytes** and contains **1,349 decoded
instructions**. The SHA-256 digest of `bytecode.hex`, including its canonical
final newline, is
`98e85e775aab17132a4008b898f4cf5696dcc64c13a73cf0bce8c775ad5ced46`.
The SHA-256 digest of the decoded 1,802 raw bytes is
`d44a9855c1201115d0b172362b5298fd37e0a0bbece9fe8ba801039e6636b6e6`.

`Bytes.lean`, `Bytecode.lean`, and `Artifact.lean` freeze and reconstruct those
same bytes. The high-index routines are proved as exact located instruction
blocks, with explicit valid-jump-destination certificates. `BigHelpers.lean`
defines the conditional returned state, proves both reduction choices,
certifies the appended MCOPY trampoline and PC-1755 dispatcher, and proves
modular representation plus disjoint-region preservation. The specialized
doubling layer proves the safe direct-return branch and the fused unsafe branch
against that helper contract. Since branch costs are data-dependent, obsolete
fixed-cost equalities are not used as correctness assumptions; `GasSteps`
composition proves existence of exact executable traces for whichever branch
the frozen bytecode takes.

The proof tree introduces no `sorry`, `native_decide`, or new axioms. It uses
only the benchmark's permitted ambient Lean axioms and executes the exact
submitted instructions rather than trusting the prototype bytecode generator.
Server CI remains authoritative for the complete exported theorem.

### Exact thirteen-vector score

The exact executable scorer accepted all thirteen vectors for the frozen
1,802-byte candidate:

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
| 257-bit modulus | 1,009,527 |
| BN254 modular inversion | 42,775 |
| random 256-bit modexp | 42,775 |
| RSA-1024 e=3 | 3,258,689 |
| RSA-2048 e=65537 | 91,098,862 |
| **aggregate** | **95,534,607** |

RSA-2048 alone falls from 146,613,339 gas in the preceding candidate to
91,098,862 gas, a 55,514,477-gas reduction. The aggregate is 49.3% below the
188,393,772 promoted frontier and 37.5% below our preceding 152,861,863
candidate.

Reproduce the executable check from the benchmark repository root with:

```sh
lake exe modexpchallenge --hex=Challenge/Modexp/Submission/bytecode.hex --csv
```

For the complete theorem and protected benchmark pipeline, use `yukon run`
after `yukon setup`; on local Darwin only, the benchmark requires the documented
`BENCHMARK_INSECURE_LOCAL=1` opt-in. The ranked Linux verifier does not use that
local-only flag.
