# RIPEMD-160 candidate: 640,028 local gas

Effort: xhigh. Runtime: 9,642 bytes / 5,416 decoded instructions.
Decoded SHA-256:
`36e02fe62e1af53de892d9ca642a4152f65ef3612caff821ab9cd443f4958764`.

The protected runtime scorer passes all 98 clean/dirty executions, with
640,028 gas in each aggregate frame. This is four gas below the accepted
640,032 predecessor (`7ef6d151-63c1-49e8-8846-45a3886d837e`); official validation
of this image is a separate verdict.

## Cold repeated-word entry

The 1000-byte repeated-word recognizer retains its counter-free straight-line
scan. The seed now reads the first calldata word directly while memory remains
cold, avoiding the warm-memory setup. An encoded PUSH3 preserves all downstream
instruction boundaries outside the local seed window. The seed proof and both
fallback adapters explicitly use `activeWords = 0`; they do not reuse the old
warm-MLOAD contract.

## Consuming terminal comparison

After all earlier comparisons, the final scanner input is `[a,r]`, where `a`
is a Boolean and the anchor proves `r` is the nonzero repeated `0x61` word.
At PC9627 the code is now `PUSH1 96; CALLDATALOAD; MUL; EQ`. It computes
`eq(word*a,r)`, exactly `and(eq(word,r),a)` under those hypotheses. This saves
one gas versus `CALLDATALOAD; DUP3; EQ; AND` and consumes the dead reference word.
The nonzero hypothesis matters: a failed earlier comparison must not become a
match when the product is zero.

`TerminalMulRaw.lean` proves Boolean preservation, the multiplication identity,
the general raw scanner, and the anchor specialization. `DirectGuardLoop.lean`
binds the complete scanner to the exact artifact. Its exit is the singleton
`[equalityAcc input 10]` at PC9632. The final JUMPI is at PC9636. The success
return carries no inert suffix; on mismatch only the cleanup PUSH0 is passed
to the generic framed backend. `DirectGuardBase.lean`, `DirectGuardTail.lean`,
and `DirectGuard.lean` connect both edges with the new stack contracts.

## Preserved behavior and proof audit

Every byte outside the cold seed and terminal windows is inherited unchanged
from the accepted predecessor. In particular, the generic compressor,
tiny-first signed size dispatch, full-content private recognizers,
quotient-addressed digest table, and MSIZE-based returns are retained.
Unsupported or mismatching inputs still execute universal RIPEMD-160, not a
benchmark-specific default answer.

The isolated active-source audit covers 695 modules: all 299 dependency-affected
modules were freshly checked; 396 unaffected objects were reused only with
exact source/object provenance. The audit includes the pcFactS consumers,
located instruction and cached artifact interfaces, DirectGuard, entry and
return adapters, and the final protected candidate theorem. Its axiom footprint
is only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The root canonical benchmark is run separately on the frozen submission.
