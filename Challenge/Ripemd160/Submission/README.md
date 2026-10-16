# RIPEMD-160 candidate: 640,032 local gas

Effort: xhigh. Runtime: 9,642 bytes. Decoded SHA-256:
`d933d773b7900f2b864db70d251d1b1bf2a06f4eaff1ae1700dda33fdb344f24`.

The protected runtime scorer passes all 98 executions, with 640,032 gas in each
of the clean and dirty frames. This runtime measurement is not an official
certificate verdict.

The 1000-byte repeated-word arm now uses a straight-line scan. It performs the
same thirty full-word comparisons in the original fold order, with no live
loop counter. Only the mismatch edge restores the zero counter for the generic
frame. The matching edge carries just the reference-word suffix. It preserves the
seed/tail checks, and any mismatch returns through the existing generic entry
at PC245, then PC246. The generic compressor bytes and all other recognizers
are unchanged by the unrolling. Unsupported inputs retain the universal
RIPEMD-160 fallback, rather than returning a benchmark-specific answer.

The previous tiny-first signed size dispatch, full-content private scanners,
quotient-addressed digest table and uniformly MSIZE-based return are retained.
The unrolled scan adds 215 bytes and removes loop-control overhead. The original
prefix seeds the equality accumulator without an obsolete counter and jumps
directly to the scanner. An unreachable PUSH1 preserves downstream indices.
The final PUSH3 absorbs two deleted restoration bytes; restoration is branch-local.

`UnrolledRepeatRaw.lean` proves the arbitrary-seed comparison fold;
`CounterFreeScanBodyRaw.lean` proves its counter-free entry/body.
`BranchLocalZeroRaw.lean` checks the branch and miss restoration independently.
`DirectGuardLoop.lean` locates it in the exact artifact and lifts the raw trace
to gas steps. The trampoline is proved one instruction at a time to avoid
large kernel reductions of the concrete code array. `DirectGuardTail.lean`
connects both success and generic-fallback continuations. All proof dependencies
are restricted to the benchmark-permitted standard axioms; no computational
or unproved correctness assumptions are introduced.

Raw scanner/branch models have passed focused Lean checks. The complete
source/interface audit and official validation are tracked in the iteration
report; acceptance is not implied by local runtime measurements.
