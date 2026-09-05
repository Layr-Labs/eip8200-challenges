# MODEXP: skip the exponent's leading zero bits (cold-path clone)

Effort: high

This submission stacks one further control-flow change on the previously
proved MODEXP artifact: the big-modulus exponentiation loop no longer does any
work for the leading zero bits of the exponent.

The thirteen scored vectors go from 330,963,223 gas to **257,663,166** gas
(1.284x on top of the previous step, 3.339x against the 860,099,031 gas of the
original artifact). The artifact grows from 1343 to 1404 bytes (995 to 1040
instructions). Exactly two of the existing bytes are rewritten in place; the
remaining 61 bytes are appended past the end of the old code.

The proof work was implemented by a Claude Opus 5 subagent; the surrounding
loop (design, byte-level construction, differential testing, orchestration) was
driven by Claude Fable 5.1.

## 1. What is being skipped

The big path runs square-and-multiply over the exponent bit by bit, most
significant bit first, with the accumulator initialised to `1 % modulus`. The
exponent is supplied as a byte string of length `|e|`, and EIP-198 does not
require it to be normalised: the caller may (and in practice constantly does)
left-pad it with zeros. `e = 65537` submitted as a four-byte string is
`00 01 00 01`, so the first fifteen of its thirty-two bits are zero.

For every one of those leading zero bits, the accepted artifact still performs
a full modular squaring of the accumulator (and, before the previous step in
this ladder, a full modular multiplication as well). But while the accumulator
still holds `1 % modulus`, both operations are identities:

```
(1 % m)^2 % m = 1 % m          and          ((1 % m) * (1 % m)) % m = 1 % m
```

for every modulus `m`, including the degenerate `m = 1` where `1 % m = 0`. So
all the work done before the first set exponent bit is provably discarded, and
the loop can be started directly at that bit.

The saving is entirely at *bit* granularity. Whole leading zero *bytes* happen
to be worth nothing on the thirteen scored vectors — the three vectors with a
big modulus have exponents whose first byte is `01`, `03` and `03` — but
skipping them is still implemented, because the artifact must be correct for
every legal input, and inputs with leading zero bytes are legal.

## 2. Why a second copy of the loop instead of a flag

The natural implementation is a predicate "have we seen a set bit yet?" tested
once per bit. Three ways to store that predicate were considered and rejected:

- **A memory flag.** Costs an `SLOAD`-free but still real `MLOAD`/`MSTORE`
  pair per bit, and — much worse for the proof — introduces a new piece of
  machine state whose relationship to the mathematical model has to be stated
  and preserved through every lemma in the exponent layer, including the
  helper routines that copy limbs around.
- **A spare stack slot.** Cheaper at runtime, but the exponent loop's stack
  frame is already threaded verbatim through several dozen lemmas; widening it
  by one word touches all of them.
- **Testing `accumulator == 1 % m` directly.** Requires an `n`-limb comparison
  per bit, which for a 2048-bit modulus is eight `MLOAD`s and eight
  comparisons — more expensive than the squaring it is trying to avoid on
  small moduli, and it needs a fresh "these limbs represent one" lemma.

The chosen design stores the predicate **in the program counter**. A clone of
the outer/inner loop pair is appended to the code; the clone's only job is to
find the first set bit. It executes no memory instruction at all, and it
reaches the hot loop by jumping into the middle of it, at the exact bit index
it stopped at. The entry point of the exponent loop is redirected from the hot
outer loop to the clone — that is the two-byte in-place edit, a `PUSH2`
immediate at offset 928.

The proof consequence is the whole point: because the cold clone touches no
memory, every `Limbs.Represents` hypothesis about the base, the modulus and
the accumulator passes through the entire cold phase **unchanged**, by
reflexivity. And because both of its branch conditions are calldata-derived
values that the existing proof already characterises (`loadedExponentByte` for
"is this exponent byte zero" and the existing `exponentBit` for "is this bit
set"), no new "what does this memory word mean" obligation is created anywhere.

## 3. The appended routine

45 instructions in 61 bytes, laid out as five blocks:

- `coldStart` (pc 1343) — pushes the byte counter and falls into the loop.
- `coldOuter` (pc 1345) — the byte guard. If the byte index has reached `|e|`
  the exponent is zero; jump straight to the result serializer, with the
  accumulator still `1 % modulus`, which is the correct answer for `e = 0`.
- The byte load and zero test — `CALLDATALOAD` plus `BYTE` to extract one
  exponent byte, then a test against zero. On zero, jump to `coldNext`.
- `coldBit` (pc 1368) — the bit loop over the eight bits of a nonzero byte,
  using the same `(byte >> (7 - j)) & 1` extraction as the hot loop, so it
  shares the hot loop's bit lemmas verbatim.
- `coldNext` (pc 1389) — byte index increment and loop back.
- `coldHit` (pc 1399) — the first set bit was found at byte `i`, bit `j`;
  build the hot loop's stack frame and jump into the hot inner loop at pc 963,
  which then processes that very bit as a normal set bit.

Every static jump target in the appended code is checked at build time to land
on a `JUMPDEST`, and the whole 1040-instruction decoding is re-derived from
the frozen bytes and compared instruction by instruction.

## 4. Cost

Per skipped bit the cold loop costs 52 gas (versus a squaring, which for an
`n`-limb modulus costs `189 + 87n + M(n)` where `M(n)` is a full modular
multiplication — for `n = 8`, roughly 480,000 gas). A skipped all-zero
exponent byte costs 87 gas for the whole byte rather than eight squarings.
Finding the first set bit inside a nonzero byte costs at most `7*52 + 35 + 12`.

On the three vectors that exercise the big path:

| vector | previous step | this submission |
|---|---:|---:|
| 257-bit modulus | 6,871,581 | 3,117,633 |
| RSA-1024, e = 3 | 29,147,058 | 16,075,350 |
| RSA-2048, e = 65537 | 294,768,707 | 238,294,306 |
| **all thirteen** | **330,963,223** | **257,663,166** |

The other ten vectors are byte-identical in gas: they either never reach the
big path, or their exponent's leading bits are already set.

## 5. Proof structure

The change is proved at the same three layers the existing artifact uses.

**Execution layer** (`BigExponent.lean`). Twelve new located blocks cover the
45 appended instructions, each discharged by `Stepper.runLocatedBlock_sound`
against the instruction table. Each of the three conditional jumps is given
its *own* block, arranged so that the tested value is already an opaque stack
variable when the block starts. This matters: if the value were computed
inside the same block as the `JUMPI`, the branch condition would appear in
whatever normal form the machine semantics produced, while the hypothesis is
stated in terms of `loadedExponentByte` and `exponentBit`, and bridging the
two would rest on simp happening to agree. Splitting the blocks removes that
dependency entirely.

**Gas layer** (`BigExponentGas.lean`). Two new recursive functions,
`coldByteIndex` and `coldBitIndex`, define where the first set bit is, with
lemmas saying that everything before it is zero and that the index is in
range. From those the cold phase's `GasSteps` trace is assembled. The hot
loop's existing iteration lemmas only ran from bit 0 / byte 0, so shifted
variants (`bitProgressFrom`, `byteProgressFrom` and their `iterateBounded`
compositions) were added, letting the hot loop be entered at an arbitrary
starting index. The two are joined into a single `gasSteps_exponentPhase`
whose endpoint is definitionally the state the serializer already expects, so
the downstream completeness proof changes only in which lemma it cites.

**Correctness layer** (`BigExponentCorrect.lean`). The mathematical core is
one line — `(1 % m)^N % m = 1 % m` follows from `Nat.pow_mod` and
`Nat.one_pow`, uniformly in `m`, with no case split on `m = 1`. Around it:
`natBitAfter_of_zero_prefix` and `exponentValueAfter_of_zero_prefix` say the
accumulator is unchanged across a zero prefix, and two splitting lemmas
(`natBitAfter_split`, `exponentValueAfter_split`) say that running the hot
loop from the first set bit computes the same value the full loop would have.
The result is that `exponentProgressState`, the statement consumed by the rest
of the proof, keeps exactly its old type and its old name.

No `sorry`, no `native_decide`; the axiom set is the ambient
`propext` / `Quot.sound` / `Classical.choice`.

## 6. Verification performed

Locally, the changed modules and their dependencies were elaborated, and the
thirteen scored vectors were re-executed on the new bytes in an independent
EVM interpreter, checking both the gas figures quoted above and that every
output equals `pow(base, exponent, modulus)` byte for byte, including the
`modulus = 0` and zero-length-modulus edge cases. Local verification was
deliberately scoped to the modules this change touches together with their
dependency closure and immediate downstream; the full proof check, including
the modules this change does not touch, is performed by the server's
comparator, which is the authority on whether the submission is accepted.
