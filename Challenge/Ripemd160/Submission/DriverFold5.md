# DriverFold5: general RIPEMD-160 computation, without stored-answer dispatch

## Status

Prepared bytecode and a deterministic, source-hash-checked proof-tree transformation.
The candidate has NOT been elaborated with Lean, replayed with Comparator, or scored
by the protected Yukon binary in the preparation environment. Do not claim an official
pass or submit merely because the independent tests pass.

Independent result for the expanded 49-vector corpus: **2,195,292 gas** on each of five
seeds. The original 17-vector subtotal is **1,113,327**. These are different corpora.
Raw bytecode SHA-256: `79f1d882fc36b0c0eaeac4446222abdb70852a3adee94fe8dbd62a9d3a9089c8`.
Size: 5,266 bytes; 2,161 decoded instructions.

## Provenance and precise contribution

The general Q4MC implementation and its universal proof source are reused from
Layr-Labs/eip8200-challenges at commit
`80de6e6a33d4e765996a0656d746e449b92fd11f` (the head of PR #370 when inspected).
That PR was pending in the post-reset queue when inspected. Its author reports a
successful local proof/Comparator result for the pre-reset workload; that claim is
not a fresh proof check of this derivative.

Credit: Xo1otl for Q4MC, GordoAR for the packed-output foundation, terrapinelf for
the footer-loop improvement, tekkac for skipping dead table initialization, and the
reference/proof-library authors. Retain the Apache-2.0 license and existing credits.

Our new change is only the three-opcode driver fold below, saving **5 gas per padded
block**, or **645 gas over the expanded suite's 129 blocks**. The much larger gain
relative to the temporarily restored, slower post-reset entry comes from reusing the
stronger upstream general algorithm, not from this three-opcode change alone.

## Runtime delta

At instruction indices 785, 787, 788 / byte PCs 0x646, 0x648, 0x649:

```
PUSH1 64; DUP2; ADD; SWAP1; POP
PUSH1 64; JUMPDEST; ADD; JUMPDEST; JUMPDEST
```

Before the block the top two values are `[offset, paddedLength]`. The old sequence
duplicates offset and then discards the old copy. The new sequence consumes it directly.
Both finish with `[offset + 64, paddedLength]`. The operands of ADD are reversed;
addition modulo 2^256 is commutative, and the existing calldata-fit bounds already
provide the stronger no-wrap bound used by this driver proof.

The JUMPDEST instructions are executed one-gas no-ops. They keep every instruction
index and byte PC unchanged. The set of valid jump destinations DOES gain these three
positions; it is not claimed unchanged. No existing jump target or PUSH immediate changes.
The stepper's exact-bytecode proof must establish all executed control transfers again.

The new code retains all padding, the 160 RIPEMD rounds per block, cross-line combination,
and output serialization. It contains no input-identity dispatch and no precomputed digest
return. Empty calldata also performs the algorithm's padded compression block.

## Proof-source delta

`prepare.py` obtains the pinned general source tree and checks Git blob identities.
It patches only these four pre-existing source files:

- `bytecode.hex`: three byte replacements.
- `Bytes.lean`: the same replacements in reducible byte-array chunks.
- `Proofs/Bytecode/Artifact.lean`: the same three instruction opcodes and byte certificates.
- `Proofs/Bytecode/DriverTrace.lean`: three located operations and the ADD operand-order lemma.

It also adds this explanatory note and a warning above the inherited historical README. The existing `Solution.lean` continues to export
`Challenge.Ripemd160.Benchmark.candidate` through `StackCorrect.correct`. The original
`Correct` predicate, calldata quantifiers, generated benchmark bytecode, dependencies,
scorer, and workflow are not changed. There are no new axioms, proof admissions, or
native-decision shortcuts in this delta. A symbolic gas-bound theorem is NOT supplied.

The mandatory proof must still be rebuilt and replayed. Updating source certificates
and passing a Python evaluator are not substitutes for that check.

## Independent evidence

630 complete executions of each of the upstream base and candidate were checked against
hashlib/OpenSSL RIPEMD-160. The corpus includes the 17 focused inputs, 32 generated inputs
on each of five seeds, random data, structured values, and mutations. All comparisons
passed. All 46 same-length content-variation groups had equal gas and equal control-flow
fingerprints. Every tested input executed exactly its required number of compression blocks.
All measured savings equalled 5 times the padded-block count.

The interpreter was separately cross-checked against the official, already-published
49-vector diagnostic artifact of workflow 33989910747: all 49 outputs and all 49 individual
gas figures matched. That run belongs to upstream submission 464cb31e, NOT this candidate.
No official dirty-frame execution or universal gas-independence theorem for this candidate
is claimed. The protected scorer must test the actual clean and dirty frames.
