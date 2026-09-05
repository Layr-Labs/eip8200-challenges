# RIPEMD-160: straight-line output serialization

Effort: xhigh

## Base and attribution

This candidate is rooted at submission `9d2f71ad` by `GordoAR`, the promoted
frontier of this track at the time this tree was taken, at source `e6291c7`.
Everything in this tree except the output stage is that submission's work or
the work it inherits.

An earlier revision of this same change was built on an unpromoted candidate
that was in validation at the time. That candidate did not pass, so this tree
was taken again from the promoted frontier and the change re-derived on it
from scratch: the artifact was regenerated, the entry and return addresses
recomputed against the new byte layout, and every check below re-run on the
result. Nothing was carried across from the abandoned revision. This is stated
plainly rather than left implicit, because the two bases differ in more than
address arithmetic — they differ in the memory high-water mark they reach on
one vector, and the check named below was re-run against the correct one.

Through its lineage the base carries the promoted chain that produced the
current design — the stack-resident compressor and its paired round helpers,
the packed message schedule, the unmasked multiplication folds, the Boolean
jump table and selection identities, the unaligned table windows, the
stack-consuming helper convention, and the direct entry jump — contributed by
`GordoAR`, `ercumentyildirim`, `terrapinelf`, `may93182`, `mpjunior92` and
`saucegodbased`. None of that is claimed here. Everything outside the output
stage is carried forward unchanged.

Promoting this candidate replaces the track's editable path with this tree
wholesale, so any edit made to that path in the meantime is not carried
forward. We hold no promoted submission on this track, so nothing of our own
is displaced; what would be displaced is any submission promoted between this
tree being taken and this one being accepted. Two other tickets were in
validation when this was prepared, and if either lands first this one should
be re-cut on it rather than promoted over it.

## Scope of change

The change is confined to the routine that produces the 32-byte return value.
Nothing in the padding, the block driver, the message schedule, the
compression core, the round helpers, the chaining-value update or the entry
dispatch is touched.

The promoted program serializes the result with two nested loops. An outer
loop runs five times; each pass calls a helper to load one chaining word and
then calls a four-iteration inner loop that places that word's bytes one at a
time with `MSTORE8`. Between them the two loops perform five helper calls,
five return jumps, twenty inner iterations with their own tests and counter
updates, and the surrounding call and return plumbing.

This candidate replaces that with one straight-line routine, appended past the
end of the program and entered by rewriting a single `PUSH2` payload. The
routine zeroes the return window, then for each chaining word loads it once
and places its four bytes with `MSTORE8`.

**The writes are the same writes.** Each `MSTORE8` stores the same byte value
at the same address as the corresponding write in the loop, and they are
performed in the same order. What is removed is the loop control, the helper
calls and the return jumps around them — not any store.

## Preserved surface

| property | before | after |
| --- | --- | --- |
| bytes | 4,980 | 5,139 |
| instructions | 2,473 | 2,586 |
| 64-byte artifact chunks | 78 | 81 |
| bytes changed in the existing program | — | **two**, the payload of one `PUSH2` |
| every other program counter and instruction index | — | identical |
| every jump destination in the existing program | — | identical |
| memory image of the return window | — | byte-for-byte identical |
| active-word count, per vector | — | identical on all seventeen |
| public `Challenge.Ripemd160.Correct` contract | — | unchanged |

Because the appended routine performs the same stores, the state it reaches is
the state the loop reached, and every layer above the output stage — the
functional bridge from the written window to the specification digest, the
padded-block bridge, the compression seam and the final correctness theorem —
consumes it unchanged.

The replaced loops remain in the program at their original addresses. They are
no longer reachable, and their own certificates continue to elaborate against
the artifact, so no proof obligation was removed to make room for this one.

## Proof

The appended routine is a single basic block, so it is certified as one
located instruction path against the artifact's structural certificate, and
its execution is the composition of that path's steps. Two supporting facts
are worth naming:

- the routine's entry is proved to be a valid jump destination through the
  artifact's instruction index rather than by scanning the byte array, which
  is the form the rest of this tree uses for jump destinations; and
- the state the path reaches is stated as the *existing* description of the
  post-serialization state, so the functional obligation above it is
  discharged by the proof already present rather than restated.

`Bytes.lean` and the structural certificate `Proofs/Bytecode/Artifact.lean`
were regenerated from the submitted bytes, and the artifact's assembly
certificate re-elaborates against them. `Solution.lean` and the public
correctness contract are unchanged. The transitive axiom footprint of the
exposed theorem stays inside `propext`, `Quot.sound` and `Classical.choice`,
with no fourth axiom and no unfinished-proof placeholder anywhere in the
closure. No kernel-reduction or decision-procedure escape hatch is used, and
there is no vector-specific branch.

## Packaging

- `bytecode.hex` is one line of canonical lowercase byte pairs with no `0x`
  prefix and a trailing newline.
- Only files under the track's declared editable path
  `Challenge/Ripemd160/Submission` are modified.
- No protected specification, proof support, evaluator, scorer, vector,
  workflow or Comparator source is touched.

## Validation performed

- The exact submitted bytes were executed on all seventeen public vectors by
  the protected scorer, from both the clean and the dirty initial state, with
  the correct digest and equal paired results on every one.
- The same bytes were executed over an additional suite of randomized and
  boundary inputs spanning every padding boundary and block count reachable by
  the scored sizes, and matched a reference RIPEMD-160 on all of them.
- The active-word count after every one of the seventeen vectors was compared
  against the base and is identical on all seventeen, so no memory term moved.
  This was checked against the promoted base this tree is rooted at, not
  against a neighbouring lineage, because the two disagree on one vector and
  the wrong comparison would have hidden a real change.
- The byte written at every address in the return window was compared with the
  byte the replaced loop writes there.
- The complete dependency closure of the exposed theorem was rebuilt on the
  pinned toolchain, and the axiom footprint was checked after that build
  rather than in isolation.
- The submitted hex and the byte array the theorems are stated about were
  compared for equality.
- This note was checked for credentials, tokens, hostnames, private paths and
  personal data before upload.

Executable vectors are a falsification check only. The protected Comparator's
acceptance of the universal Lean theorem for these exact bytes, followed by
the protected scorer, remains the acceptance condition.
