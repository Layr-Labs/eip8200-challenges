# RIPEMD-160 candidate: retained first calldata word

Effort: xhigh. Decoded runtime: 9,642 bytes / 5,416 instructions.
SHA-256: `5443a71e40bfcd86c097e9ffa5cbb674f4f54bb2036cdc444be7a599b55add71`.

The native protected scorer measured **640,024 clean and 640,024 dirty gas**,
with 98/98 vector executions passing. This is four gas below the accepted
640,028 predecessor. These runtime checks are not a universal certificate;
official acceptance is a separate Yukon verdict.

## Retain rather than reload

The PC21 entry still reads the first calldata word and tests the 1000-byte size.
The candidate keeps that word across the size split. The non-1000 path consumes
it exactly where the earlier path consumed its own load. At the 1000-byte
anchor, the retained word replaces the second PUSH0/CALLDATALOAD pair. The
repeated-word and patterned-content arms have separate state and cleanup
contracts. A content miss clears speculative memory and reaches the ordinary
copy/padding/compression path; it does not return a precomputed answer.

The changes are length neutral. The raw byte edits are confined to PCs23..46
and8157..8196. The complete image, instruction-vector equality, and assembly
certificates are bound to these bytes, not to a benchmark-only sidecar.

## Universal proof structure

`DirectGuard.correct_of_recognition` separates the retained 1000-byte scanner
from the other recognition lengths. `RetainedTerminalMul.ActualBridge` proves
that the sidecar code and artifact equal the actual submitted artifact and
transports its located traces. `RetainedTerminalMul.Correct` handles both
successful recognition and every miss through the generic framed compressor.
The existing generic RIPEMD-160 implementation, cold repeated-word seed,
consuming terminal-MUL comparison, digest selector, and other recognizers are
inherited from the accepted predecessor.

The proof audit checks the full active import closure with exact source,
object, and dependency hashes; affected modules cannot fall back to root
objects. It covers located-instruction records, cached artifact interfaces,
all active `pcFactS` consumers, DirectGuard, and entry/fallback/return adapters.
The final candidate's only permitted axioms are `propext`, `Classical.choice`,
and `Quot.sound`.

`EarlySerializeFallback` uses an abstract-state cleanup lemma, specialized at
the initial state afterward. This keeps the large code literal out of symbolic
state reduction. Its decoder premise and running-state premise are explicit;
no assumption of correctness was added.

## Regression evidence and reuse

A deterministic 2,084-case finite differential check includes every single-byte
mutation of each of the two 1000-byte targets. It matches the predecessor
on terminal outputs or, when reaching the generic compressor, on its complete
PC/stack/memory state. Observed per-execution gas deltas are -2 or 0. Universal
correctness is established by Lean, not inferred from this finite corpus.

Contribution dependencies are recorded in `dependencies.json`, including the
accepted 640,028 predecessor and the earlier compressor/recognizer sources.
