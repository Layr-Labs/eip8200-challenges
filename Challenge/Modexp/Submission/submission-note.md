# MODEXP: the first set exponent bit needs no squaring

Effort: high

This submission is a two-byte change to the previously accepted MODEXP
artifact. The artifact length, the instruction count, and every instruction
boundary are unchanged: a single `PUSH2` immediate is rewritten in place.

The thirteen scored vectors go from 257,663,166 gas to **246,790,985** gas
(1.044x on top of the previous step, 3.485x against the 860,099,031 gas of the
original artifact).

This submission was produced with Claude Opus 5 running in Claude Code:
subagents did the analysis, byte-level construction, differential testing and
the Lean proof, coordinated by an orchestrating session.

## 1. What is being skipped

The previous step added a cold clone of the exponent loop whose only job is to
find the first set exponent bit, so that the leading zero bits cost 52 gas each
instead of a full modular squaring. Having found that bit, at byte `i` and bit
`j`, the clone built the hot loop's stack frame and jumped to the hot inner
loop head at pc 963, so the bit was then processed as an ordinary set bit: a
full `mulModBig(ACC, ACC)` squaring, a `copyLimbs`, and a full
`mulModBig(ACC, BASE)` multiply.

But the accumulator at that moment is still `1 % modulus` — that is exactly
what the cold clone establishes, since every bit before this one was zero and
the clone touches no memory. So the squaring computes

```
((1 % m) * (1 % m)) % m = 1 % m
```

for every modulus `m`, including the degenerate `m = 1` where `1 % m = 0`. It
is the identity, and it costs a complete `mulModBig` — 8,066,948 gas for an
eight-limb modulus, once per call.

The hot bit step is laid out as two consecutive blocks: the square-and-copy
sub-phase, then the branch at pc 1284 which either falls through (bit clear) or
jumps to pc 1297, the block that performs only the multiply. The stack at
pc 1399, where the cold clone lands, is

```
[j, byte, off, i, modulusOr, n, bsize, ...]
```

which is byte-identical to the stack the branch hands to pc 1297. So the cold
clone's final jump is simply retargeted from 963 to 1297: it enters the bit
mid-way, after the squaring it is entitled to skip.

## 2. The edit

Two bytes, at offsets 1401 and 1402:

```
1400: 61 03 c3   PUSH2 963     ->   61 05 11   PUSH2 1297
```

Nothing is inserted, deleted, widened or moved. The artifact stays 1404 bytes
and 1040 instructions, and every instruction index in the existing proof stays
valid; only one immediate's value changes.

## 3. Cost

Per call on the big path, one `mulModBig(ACC, ACC)` and the `copyLimbs` that
follows it are removed. That is a fixed saving per call, not per bit, so it
grows with the modulus and is independent of the exponent length.

| vector | previous step | this submission |
|---|---:|---:|
| 257-bit modulus | 3,117,633 | 2,491,930 |
| RSA-1024, e = 3 | 16,075,350 | 13,896,687 |
| RSA-2048, e = 65537 | 238,294,306 | 230,226,491 |
| **all thirteen** | **257,663,166** | **246,790,985** |

The other ten vectors are byte-identical in gas: they never reach the big path.
For the eight-limb RSA-2048 modulus the saving is 8,067,815 gas, which is one
`mulModBig` plus one eight-limb `copyLimbs` almost exactly.

## 4. Proof structure

Three of the fifty-nine proof modules change; the other fifty-six, including
the whole multiplication, copy, base, serializer and header layers, are
untouched.

**Execution layer** (`BigExponent.lean`). `coldHitPath`'s `PUSH2` immediate
becomes 1297 and `run_coldHit` now lands on `bitMulEntry`, a new state
constructor for "at pc 1297 with the bit tail frame on the stack", taken from
an *arbitrary* machine state rather than from the post-squaring state the hot
loop happens to be in. `run_productCall` and `run_copyBack` are generalised the
same way (`run_productCallAt`, `run_copyBackAt`), so the multiply-only block
has one set of block lemmas serving both entries.

**Gas layer** (`BigExponentGas.lean`). One new composite,
`gasSteps_bitMulTail`, runs the multiply-only half of a bit step from an
arbitrary entry state to the inner loop at the next bit. The cold phase's
hand-off state `coldPhaseHit` becomes the state that composite leaves behind
rather than the untouched entry state, and `coldPhaseStart` becomes `j + 1`
rather than `j`: the bit the cold search stopped on is now fully processed by
the hand-off, so the hot loop resumes after it. `gasSteps_exponentPhase` gains
exactly one `.trans` in its chain. The shifted hot iterators
(`bitProgressFrom` / `byteProgressFrom` and their `iterateBounded`
compositions) added by the previous step already accept an arbitrary starting
bit index, so nothing there changes.

**Correctness layer** (`BigExponentCorrect.lean`). The mathematical content is
`oneMod_pow` — already in that file — instantiated at `N = 2`:
`(1 % m) * (1 % m) % m = 1 % m`, uniformly in `m`, with no case split on
`m = 1`. Around it, `natBitAfter_succ_of_zero_prefix` says that running the
first `j + 1` bits over `1 % m`, with a zero prefix and a set bit at `j`, is
just `(1 % m) * base % m`; and `bitMulCopyBack_represents` says the
multiply-only block computes precisely that in the accumulator region while
leaving the base and modulus regions alone. `coldPhaseHit_represents` keeps its
name and its type, so `exponentPhase_represents` — and everything downstream of
it — changes not at all.

No `sorry`, no `native_decide`; the axiom set is the ambient
`propext` / `Quot.sound` / `Classical.choice`.

## 5. Verification performed

The changed modules and their dependency closure were elaborated locally, and
the thirteen scored vectors were re-executed on the new bytes in an independent
EVM interpreter, checking both the gas figures above and that every output
equals `pow(base, exponent, modulus)` byte for byte. The new bytes were
additionally fuzzed against that interpreter over roughly 6,300 capped random
cases, 1,500 wider-grid cases including odd limb counts, and 1,440
truncated-calldata cases exercising EIP-198's trailing-zero semantics. The full
proof check, including the modules this change does not touch, is performed by
the server's comparator, which is the authority on whether the submission is
accepted.
