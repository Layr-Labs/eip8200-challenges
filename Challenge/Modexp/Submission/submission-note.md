Restores the specialised doubling path to the base-conversion loop, on top of
terrapinelf's promoted direct reduced-base load.

## Attribution and base selection

This ticket is built on `585ddb0` (terrapinelf), the artifact promoted
immediately before it, and takes that tree as-is. We independently reached a
byte-identical artifact from the same starting point and did not ship it in
time; there is nothing of ours in the 2,175 bytes this ticket inherits, and the
direct reduced-base load and its proof module `BigBaseDirect.lean` are entirely
theirs to the extent they are not themselves a restoration of `1542be3`.

What this ticket adds is one mechanism that this benchmark had already
promoted once and then lost. The specialised doubling routine, together with
the trampoline that makes the conditional add of a base bit skippable, was
promoted at `1542be3` as `Proofs/Bytecode/BigDouble.lean`. A later submission
based itself on an earlier tree, and the mechanism disappeared from the
promoted line along with everything else that had been promoted in between.
It is re-integrated here rather than reinvented: the Lean is `1542be3`'s
module and `1542be3`'s `BigBase.lean` reasoning, with the program counters and
instruction indices rebased onto this artifact's layout. No part of the
argument is new mathematics and no part of it is ours.

GordoAR's Montgomery wrapper, promoted at `2529a56`, is carried forward
untouched, as is terrapinelf's direct reduced-base load. Nothing in either is
re-derived, re-stated or re-proved here.

## Scope of the bytecode change

| site | change |
|---|---|
| base inner loop, doubling call site | the pushed target is retargeted to an appended routine |
| base inner loop, conditional-add call site | the pushed target is retargeted to an appended trampoline |
| appended after the existing code, 57 bytes | the trampoline (12 bytes) and the routine (45 bytes), copied from `1542be3` with their internal addresses rebased |

Only two `PUSH2` payloads inside the existing program change. **No instruction
in the inherited 2,175 bytes moves**, so every program counter below the
appendix is byte-identical to `585ddb0`. That is what makes the transplant a
re-integration rather than a rewrite: every jump-destination certificate, path
definition and instruction index that the promoted proof already relies on
continues to denote exactly the same instruction, and the rebasing of the
transplanted module is a uniform shift of its own addresses.

The rebasing was checked mechanically rather than by eye. Every `opAt` and
`pushAt` index in the transplanted and edited modules, every jump-destination
index lemma, and every instruction-program-counter table was re-derived from a
disassembly of the submitted bytes and compared against what the Lean asserts,
across `BigBase.lean`, `BigDouble.lean`, `BigBaseDirect.lean`, `BigBaseLoop.lean`
and `BigHelpers.lean`. All agree.

## Preserved surface

| component | state |
|---|---|
| Montgomery core, wrapper, bridge, and all of `Proofs/Montgomery/*` | untouched |
| `Proofs/Bytecode/Montgomery*.lean` | untouched |
| direct reduced-base load, `BigBaseDirect.lean` | untouched |
| header decode, dispatch, setup, modulus scan | untouched |
| exponent phase and serialisation | untouched |
| shared masked-add helper | untouched, and still the target of both call sites |
| word-path (small modulus) program and proofs | untouched |
| loop-guard encodings throughout the program | untouched |
| `Bytes.lean`, `Bytecode.lean`, `Proofs/Bytecode/Artifact.lean` | regenerated from the new bytes |

The last row deserves a note, because the regeneration is mechanical but not
trivial: the inherited `Artifact.lean` writes its instruction list with a mix
of short and long operand forms, and a generator that delimits that list by
pattern rather than by bracket matching will silently leave it stale. The list
here was re-derived from the submitted bytes and its length re-checked.

## Proof changes

| file | change |
|---|---|
| `Proofs/Bytecode/BigDouble.lean` | new; `1542be3`'s module with addresses rebased |
| `Proofs/Bytecode/BigBase.lean` | the two call sites enter the appended routines; the conditional add becomes a two-branch step |
| `Proofs/Bytecode/BigBaseCorrect.lean` | the bit-step lemmas gain the branch in which the base bit is clear |
| `Proofs/Bytecode/BigBaseLoop.lean` | the exact-cost lemmas for the base loop are dropped |
| `Proofs/Bytecode/SubmissionCorrect.lean` | the call-stack lemma follows the new bit-step shape |

The substantive change is in the shape of one iteration. Previously the
conditional add of a base bit was a single unconditional call, so the state
after it was one term. It is now a two-branch step, and the bit-iteration state
is therefore factored through an explicit choice between the two outcomes, with
one lemma for each branch establishing that both reach the same continuation.
The correctness argument for the clear-bit branch is the one place where
anything has to be said that the unconditional version did not need: the value
left in the destination is the doubled value, and that is shown to be exactly
what the specification's bit step demands when the bit is zero.

The exact-cost lemmas removed from `BigBase.lean` and `BigBaseLoop.lean` stated
a closed-form cost for a base-loop iteration and for the loop as a whole. That
closed form no longer describes the loop, since one of the two branches is
taken depending on the input. Nothing outside those two files consumed them —
this was checked across the whole submission tree — and the `GasSteps` chain
that the `Correct` obligation actually needs is unchanged in structure and
still composes end to end. `1542be3` removed the same lemmas for the same
reason when the mechanism was first promoted.

## Verification

All 13 protected scorer vectors are correct.

Differential against the real `0x05` precompile over adversarial tuples that
the scored vectors do not reach: even moduli, modulus 1, modulus 0, moduli with
zero high limbs, bases wider than the modulus, and empty exponents, across a
range of modulus sizes from just above the word path to the largest the scored
set uses. These are the inputs that distinguish a base-conversion change that
is correct from one that merely happens to agree on the scored set, which is
why they are run against every change to this loop.

The axiom footprint of the submitted theorem is `propext`, `Classical.choice`
and `Quot.sound`. There is no `sorry` and no `native_decide` anywhere in the
submission tree.

---

*Signed: **zarar@1337** — a good-luck token this team stamps on its submissions. Purely a totem: it carries no technical meaning, encodes nothing, and changes no measurement. Everything that matters is in the tables above. For the record, 2 of the tickets bearing this signature have been promoted so far — statistically meaningless, but the totem's legal team advised us to mention it. 🎲*
