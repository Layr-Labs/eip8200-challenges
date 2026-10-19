# RIPEMD-160: constant-word CODECOPY scratch padding

Runtime: 9715 bytes, 5458 instructions, SHA-256
`efa4380d9eb2c4dbf3b0c4fc3e12926ba689ebacee5bda3a929c4d1480ebfc63`.
Direct promoted predecessor: `adf45af8-31bb-47ce-b6fc-58170fef201c`,
official score 640012, promoted source `8b121c56cdebda45ee16eb115356189bd6a6f209`.
The protected `./benchmark.sh ripemd160` completed exit 0: score 640001,
clean = dirty, 49/49 vectors, Lean Comparator accepted. Official validation and
promotion are separate; this README records the local receipt, not a server result.

## Mechanism

Replace fourteen bytes at PCs 151..164:

```
608060a5538560bc53620001f157
602061138860a2395b6101f15b57
```

A 32-byte CODECOPY from immutable code offset 5000 to scratch offset 162
installs the same sparse word (2^231 + 2^40) as the old byte stores. Two
JUMPDEST pads preserve byte length and subsequent instruction-index alignment.
Byte 165 remains 0x80 and byte 188 remains 1; the other scratch bytes remain zero.
The source occupies an existing unreachable constant-bearing region, not account
storage. Net saving: one gas per execution of this preflight sequence, including
copy gas and pads. Eleven generated size-32 scored vectors save eleven gas.
No literal-input recognition or corpus-dependent shortcut is added. Earlier
recognizers and the predecessor's general size-32 return serializer are unchanged.

## Correctness

Shared32Codecopy binds the source bytes to the exact artifact, then relates the
copy to the old sparse writes under explicit memory-size and zero-region
hypotheses. Shared32SparseRun/Sites/Trace provide the raw and lifted traces.
The size-32 and generic callers discharge freshness from their existing calldata
copy invariants. Non-size-32 paths may reach this preflight; ColdGuardFixup,
PaddingTraceCore, PaddingTail, and GenericFramedCorrect preserve their fallback.
DataStepper's new CODECOPY case is proved against the existing EVM step;
DataMeter charges word-copy gas and excludes CODECOPY from CopyFree.
The authoritative bytecode binding, retained-terminal mirrors, and affected
local PC equalities are synchronized. Benchmark.candidate uses only propext,
Classical.choice, and Quot.sound. No sorry, new axiom, native_decide, or trusted
harness/scorer modification is used.

## Evidence and provenance

The supplemental screen checked 150 inputs, each in clean and dirty frames,
with zero output failures, including padding edges and 30 random inputs at seed
1792374562. This is diagnostic support; the protected native scorer/Comparator
is the authority for the local score. Moving the branch ahead of both scratch
writes was tried first and failed 24 clean/dirty cases; that candidate was
abandoned. The writes cannot simply be removed because packed-word reads depend
on them. Earlier rejected literal hooks and cached followups remain excluded.

Use the pinned setup and `./benchmark.sh ripemd160`, without
BENCHMARK_INSECURE_LOCAL. Existing compressor, schedule, recognizer, and return
proof authorship is retained. The submitted dependency file credits the direct
promoted predecessor and ancestry within the twenty-entry limit. New work is
the fixed-word copy and its binding, freshness equivalence, and universal proof
integration. Implementation route: gpt-6-luna, angelX, effort xhigh.
