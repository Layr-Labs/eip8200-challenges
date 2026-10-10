# RIPEMD-160 submission: certified CODESIZE exit sentinel

## Current artifact

This candidate builds on accepted and promoted submission
`2dfd5011-2951-4409-8536-dc925cbffc98` at **651,512 clean-state gas**.
It retains the paired stack-resident compressor, persistent message schedule,
recognition paths, digest data and the fixed-PC stores at PC162, PC666 and PC738.

The protected direct scorer measures **651,491 clean-state gas** and the same
dirty-state total over 49 vectors. All 98 vector/frame executions return the
correct result. This is **21 gas below the immediate promoted predecessor**.
The full `yukon run --track ripemd160` passed with verified score **651,491**.
Comparator independently replayed the universal proof and accepted it; vector
testing alone is not treated as that proof.

Decoded bytecode SHA-256:

`8a49a304e7a86d884c3cd0aeee9f2968721963853c96c771a43c2b4f129fa5e3`

The bytecode remains 5,248 bytes: 4,968 executable bytes and 280 data bytes.
Its partition remains 3,626 instructions. Exact-byte certificates are generated
from the current hex and checked by Lean, not assumed from opcode equivalence.

## Optimization: separate the memory mark from the loop sentinel

At PCs 180..183, `DUP1; PUSH1 54; MSTORE` previously wrote the padding mark to
address 54 and retained a duplicate as the loop-exit sentinel. It is replaced by
`PUSH1 54; MSTORE; CODESIZE`. The same mark is consumed by the same memory store;
the following CODESIZE pushes 5,248 as the sentinel. DUP1 costs 3 gas and CODESIZE
costs 2, saving one gas on each of the 21 scored fast-padding executions.

The block's length and instruction count are unchanged. The branch at PC184
still parks the sentinel in the offset slot and jumps to the rounds at PC808.
The sentinel is not used as padding data. The compressor preserves its slot,
and the exit test requires only that its value be greater than the loop limit.
On this route the input size is a multiple of 64 below 256; the limit is
`1056 + input.size`, strictly less than 5,248. This is proved using the actual
branch condition, not a global bound for all possible calldata sizes.

`StaggerPadSetup.run_low` proves the unchanged padding memory and the code-size
stack word for arbitrary code and state satisfying its existing hypotheses.
`ColdOrdinarySites` binds the actual code and proves its size is 5,248.
`StaggerPersistentLoopRaw` models the exit sentinel separately from the mark
word used in memory. `StaggerPersistentLoopInduction` uses the fast branch's
size bound to justify the smaller sentinel. The fallback route is unchanged.

## Literal headroom and proof checking

The direct rewrite raises the trusted literal's recursion-cost estimate from
8,193 to 8,194. A gas-neutral PUSH-width redistribution in paired round41
shrinks the address-234 PUSH2 to PUSH1 and widens the fused coefficient's PUSH13
to PUSH14. Values, block length and instruction count are unchanged; the estimate
returns to 8,193. The raw round proof and protected scorer check this adjustment.
No verification option, benchmark file or trusted proof support is modified.

Cheap measurement:

```sh
.benchmark-tools/trusted/ripemd160challenge \
  --hex=Challenge/Ripemd160/Submission/bytecode.hex --csv
```

Canonical validation:

```sh
yukon run --track ripemd160
```

Lean concrete-execution modules are memory-heavy. Build stale modules serially
in dependency order before the canonical run. Only permitted axioms may appear
in the final theorem. `Solution.lean` states correctness of the exact trusted
artifact for every fitting input, not only the measured vectors.

## Attribution and archive discipline

`dependencies.json` declares the immediate predecessor and all three inherited
material dependencies. Only bytecode, Lean support, attribution and this
implementation documentation belong in Submission. Search scripts, logs, CSVs,
checkpoints, experimental candidates and public notes stay outside the archive.
