# RIPEMD-160 submission: certified fixed-PC stores

## Current candidate

This artifact retains the paired stack-resident compressor, message schedule,
recognition paths and digest table of the accepted 651,533-gas submission
`33955124-ad6b-4d9f-bc55-cb0ece6152b3`. It adds a fixed-PC address in the fast
padding setup, in addition to the inherited PC666 and PC738 schedule stores.

The protected direct scorer measures **651,512 clean-state gas** and the same
dirty-state total across 49 vectors. All 98 vector/frame executions return the
correct digest. This is **21 gas below the immediate promoted predecessor** and
**105 below the original 651,617-gas base**. Scorer success is not the universal
correctness proof; the canonical Yukon result is the submission gate.

Decoded bytecode SHA-256:

`33715c1ac98bc1530d8feebc1d6f89547f323fe6ca92c757f694745802347362`

The bytecode remains 5,248 bytes: 4,968 executable bytes followed by 280 data
bytes. The instruction partition remains 3,626 instructions. The exact-byte
certificates are regenerated from the current hex, then checked by Lean.

## New optimization: padding address 162

The fast padding block begins at PC130. It copies the zero suffix, constructs
the bit-length word and performs stores to addresses 162, 666, 144, 522 and 54.
These stores overlap, so their order must not be changed.

The constant `128 * (1 + 2^144)` fits in 19 payload bytes. Staging its PUSH19
immediately after CALLDATACOPY positions the address-162 instruction at PC162.
The former PUSH1 162 becomes PC, saving one gas whenever that route executes.
The other length-word address, 666, uses a widened PUSH4. Together these changes
preserve the padding block's byte length, instruction count, output stack and
memory-write order. All entry/exit PCs and downstream jumps remain unchanged.

`StaggerPadSetup.run_low` now requires the actual entry PC130 explicitly. Its
symbolic trace proves the same padding memory and output stack for arbitrary
state and calldata satisfying the existing size, offset and memory hypotheses.
`ColdOrdinarySites` supplies that fixed-PC equality at the genuine artifact
slice and lifts execution to the pinned EVM semantics. The PC address is not
assumed correct at an arbitrary relocation.

Two neutral PUSH-width redistributions in compressor rounds 21 and 33 retain
their numeric values and block lengths. They reduce the generated trusted
literal's recursion-cost estimate to 8,193, within the existing default budget.
Their raw traces and exact artifact are checked, rather than inferred from the
unchanged immediate values. No verification option or benchmark file is changed
for this optimization.

## Proof and reproduction

`Solution.lean` proves `Challenge.Ripemd160.Correct` for the exact bytes generated
by the benchmark. It uses the universal recognition/correctness closure, not an
enumeration of the measured vectors. Local raw/exact-artifact checks have passed.
The integrated closure and canonical `yukon run --track ripemd160` both passed.
Comparator accepted the exact bytes, the final theorem uses only the three
permitted axioms, and the verified score is 651,512 over 49/49 vectors.
The protected verified-bytecode copy matches this artifact exactly.

Cheap measurement:

```sh
.benchmark-tools/trusted/ripemd160challenge \
  --hex=Challenge/Ripemd160/Submission/bytecode.hex --csv
```

Canonical validation:

```sh
yukon run --track ripemd160
```

The box's concrete-execution Lean modules are memory-heavy. Build independent
modules serially in dependency order before the canonical run rather than
launching many giant literal elaborations simultaneously.

## Lineage and archive discipline

`dependencies.json` declares the immediate PC666/PC738 predecessor, the PC738-only
intermediate and the original paired-compressor base. The new work changes only
the padding setup, neutral PUSH widths and their proof/certificate plumbing.
No recognition predicate, expected digest, benchmark vector or gas schedule is
added or changed.

Only bytecode, required Lean support, dependency attribution and implementation
documentation belong in this archive. Search scripts, CSVs, logs, checkpoints,
experimental candidates and public submission notes are kept outside Submission.
