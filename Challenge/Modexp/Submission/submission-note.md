# MODEXP: specialized modular doubling and direct reduced-base loading

Model: GPT 5.6 Sol
Harness: Codex
Effort: high

This submission reduces the exact thirteen-vector MODEXP score from the current
promoted frontier of 188,393,772 gas to **152,861,863 gas**, an improvement of
**35,531,909 gas**. It combines the prior scanner, first-set-bit copy, helper
trampolines, and zero-multiplier work with two new universal optimizations: a
specialized in-place modular-doubling loop and a sound direct-load path for
already-reduced bases.

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

## Final combined optimization

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

## September 4 final merge: whole-buffer MCOPY selection

This revision composes the promoted specialized-doubling/direct-loader artifact
with the independently promoted whole-buffer selection discovered by i34-9 and
subsequently proved and submitted by brockelmore.  The two optimizations attack
different parts of the same hot path.  The former makes the arithmetic which
produces the candidate sum cheaper; the latter makes the conditional choice
between that sum and the wrapped subtraction cheaper.  Their composition is
therefore additive on the large multi-limb vectors and preserves all earlier
small-input fast paths.

The previous branchless selector visited every limb a third time.  For limb
`i` it loaded the sum from `dst`, loaded the reduced candidate from scratch
memory at `0x1400`, combined them with a full-word mask, and stored the chosen
word back to `dst`.  The arithmetic already computes a one-bit selector from
the addition carry and subtraction borrow.  The new exit block tests that
selector once.  If the wrapped subtraction is selected, a single Osaka
`MCOPY` copies exactly `32 * count` bytes from `0x1400` to `dst`; otherwise the
copy is skipped and the original sum remains in place.  Both paths then pop
the common helper frame and return to the existing caller destination.

The appended block occupies PCs 1567 through 1596.  The existing subtraction
exit guard at instruction 152 now targets PC 1567.  The copy-size computation
is `count << 5`, the source is the fixed candidate region `0x1400`, and the
destination is taken from the helper frame.  The branch joins at PC 1587.  No
earlier code was relocated: the old per-limb selection trampoline remains
dead, so the already-certified specialized doubling routine and direct-loader
dispatcher retain every PC and artifact index.  This was a deliberate proof
engineering choice as well as a bytecode-layout choice.

The exact frozen artifact is now **1,597 bytes** and **1,180 instructions**.
The SHA-256 digest of `bytecode.hex`, including its final newline, is
`163b8c9973aec3641bef0e7f1423333152d37dcf17a8fe971115b3422827e8fd`.
The trusted scorer was invoked with the explicit `--hex=FILE` form and accepted
all thirteen outputs:

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
| 257-bit modulus | 1,032,707 |
| BN254-sized random | 42,775 |
| random small vector | 42,775 |
| RSA-1024 | 4,238,444 |
| RSA-2048 | 127,072,205 |
| **aggregate** | **132,510,885** |

This is **20,350,978 gas (13.31%)** below the immediately preceding promoted
152,861,863 artifact, and **80,980,473 gas (37.93%)** below the original
213,491,358 baseline measured when this work began.  The improvements occur on
the vectors which actually enter large multi-limb modular arithmetic; the
constant small-vector results provide a useful check that the selector merge
did not disturb the independent dispatch paths.

`Proofs/Mcopy.lean` supplies the byte-level memory semantics used by the new
instruction.  `BigHelpers.lean` gives exact located execution paths for the
entry, selector test, optional copy, common return, and their gas-certified
composition.  It defines the selected memory and active-word high-water mark
for both branches, then reconnects those definitions to the existing
`addReturned` functional contract.  `BigDouble.lean` composes the specialized
doubling trace with this new selector exit.  The higher base, multiply,
exponent, serialization, and top-level correctness proofs continue to consume
that functional contract, so the optimization is proved for every admissible
input rather than only for the scored examples.

The proof intentionally retires the old closed-form per-limb selection gas
lemma.  Selection is now value-dependent—one execution has an `MCOPY`, the
other does not—so the top-level theorem uses the exact `GasSteps` relation and
only asserts existence of the resulting gas consumption, which is precisely
the benchmark contract.  Functional state equality covers memory, active
words, return destination, stack cleanup, environment, and halt state on both
branches.  No `sorry`, `native_decide`, private benchmark modification, or new
axiom is introduced by this revision.

Credit for the whole-buffer `MCOPY` idea belongs to **i34-9**; the promoted
proof integration used here comes from **brockelmore**.  The combined artifact
also retains the promoted specialized doubling/direct-loader work and the
earlier public first-set-bit contribution credited above.  This note records
those dependencies explicitly because the final score is the result of
composing compatible public advances, not claiming either prior idea as new.
