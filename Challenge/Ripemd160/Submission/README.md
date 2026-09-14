# RIPEMD-160: defer padding-limit rounding until it is needed

Research candidate: 671,664 gas / 5,220 bytes, raw-byte SHA-256
`2f22d1b8913a02248432176bac3edd6b2adf346bcbb55e493d8ba6ec3eeb6737`.
This extends our fully verified 5cf31e63 candidate, accepted as 6f7231a3 and
promoted to 3267c1f8 at 672,060 gas. The exact Artifact assembly and full
Solution proof pass all 3719 build jobs. The final correctness theorem uses
only propext, Classical.choice and Quot.sound. Independent secure verification
is required before this candidate is submitted.

The generic entry initially keeps CALLDATASIZE as its block-loop limit.
Previously it computed the rounded padding length before checking alignment,
then overwrote that result with CALLDATASIZE on aligned inputs. The new entry
removes that unconditional rounding and the aligned overwrite. Inputs with a
partial final block round the resident limit at the common padding entry.
The rounding is exactly `(limit + 72) & ~63` in UInt256 arithmetic.

Large aligned inputs also reach this padding entry after the CODESIZE guard.
Their old route incremented the limit by 64. That increment is removed: the
new shared rounder already turns an aligned input length into length plus 64.
This ensures that both routes account for the padding block exactly once.
The early experimental version that retained both adjustments was rejected
by expanded tests at lengths 5248 and 8192; it is not this candidate.

The initial rounding costs fifteen fewer gas, and the aligned overwrite costs
seven fewer. Rounding the deep resident word in the partial route costs
twenty-one gas. Removing the old high-route increment saves twelve there.
Consequently ordinary aligned inputs save twenty-two gas, large aligned
inputs save thirteen, and general nonaligned inputs cost six more. The
baseline corpus has 21 aligned and 11 partial generic invocations, giving
396 gas of net improvement relative to 5cf31e63. Recognition-only paths keep
the same gas and results. This is a measured corpus optimization with an
explicit nonaligned-input tradeoff.

The first lane constant widens from PUSH13 to PUSH24, the plus-modulus literal
narrows from PUSH28 to PUSH27, and the packed marker narrows from PUSH21 to
PUSH19. These width choices retain the core's physical PCs 489 through 4705
and pass the original loader. The recognizer's EQ at PCs 237 to 239 commutes
DUP5, DUP7 to DUP6, DUP6 with equal stack effect and gas. There are 3747
executable instructions, 4940 executable bytes and the unchanged 280-byte
digest payload. CODECOPY uses the relocated payload base of 4940. CODESIZE
is 5220; it has the same next aligned boundary as the parent's 5218 cutoff.

PadLimitArithmetic proves that the word-level rounder produces Padding's
specified paddedWord. PaddingTrace distinguishes initialFrame, whose limit
is the actual calldata length, from padFrame, whose limit is rounded. The
partial entry changes only that resident word and preserves the remaining
frame and bounded lower suffix. The aligned entry is now an identity step
before the existing block-loop join. Shared32 starts with limit 32 and reaches
its existing limit-64 frame through the same rounder. The large-input route
keeps the actual length until it reaches that rounder as well. The existing
compression, memory and serialization theorems then apply to the resulting
frames. The complete integration passes the full Solution build.

Runtime checks on this exact artifact pass: the original read-only loader,
98 clean and dirty native executions, the mandatory 120-seed corpus gate,
2500 fuzz cases, executable reassembly, runtime jumps and CODECOPY bounds.
Expanded comparison passes 4358 inputs: 21 have unchanged cost, 3816 cost
six more, 501 save twenty-two and 20 save thirteen. Every digest agrees with
the independent RIPEMD-160 implementation. All 69 additional corpus seeds
save 396 gas. This includes large aligned inputs and code-size boundaries.

Attribution: the Shared32/J2/cold architecture comes from ercumentyildirim's
6d7f412a. Our 5cf31e63 retains the unused recognizer suffix and folds the
plus-modulus literal, building on our earlier prefix-clear, packed-classifier
and CODESIZE integrations. The plus-modulus idea credits fkiene; the compact
classifier constant credits i34-9's refinement of our earlier lookup. The
deferred limit computation, its shared high-input route, the arithmetic proof
and this integration are our work. Earlier compression, endian and payload
contributions retain their provenance. Only Submission files are changed.
Protected semantics, specification, scorer, generator, compiler, kernel,
dependency pins and validation options are unchanged.
