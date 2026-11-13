# RIPEMD-160: three padding-word folds and two shuffle removals per compression

This candidate stacks two independent local savings on the promoted
616,790-gas parent and keeps the bytecode at 10,511 bytes.

**Padding folds (18 gas per padding block).** Every input whose length is a
multiple of 64 bytes ends with a constant padding block, compressed by a
specialised routine whose message words are literals. In paired rounds 0, 65
and 73 of that routine a non-zero padding word was still added in its own
step (`PUSH word; ADD; DUPn; ADD`, with the round key copied from the stack).
The candidate pushes the precomputed `key + word` instead, so each of the
three rounds loses one `DUP` and one `ADD` (6 gas). Rounds 0 and 65 grow by
one byte each and round 73 shrinks by two, so the routine keeps its length.

**Shuffle removals (3 gas per compression, both compressors).** Round 49
computes its rotation with `MULMOD`; its two cached constants are now copied
in round 48, where the top of the stack is rebuilt anyway, so round 49 no
longer needs a `SWAP2`. Round 16 no longer discards the old round key with
`SWAP6 POP`: round 15 swaps the new key into the key slot while it adds the
old one (`PUSH22 key SWAP9 ADD`). Each change removes one instruction; a
`JUMPDEST` fills the freed byte so later program counters and jump targets
stay put. Net: 2 + 1 gas per compression.

**Byte layout.** Four commutative operand pairs (`DUPa DUPb OP` rewritten as
`DUP(b-1) DUP(a+1) OP`, same gas, same result) keep the protected generated
`Benchmark/Artifact.lean` compilable: it only compiles while code length
plus the sum over its 64-byte chunks of distinct byte values stays at or
below 15,066. This layout has 10,511 + 4,554 = 15,065.

Every byte from offset 9,711 on, including the 32-byte path and the
code-copied table data, is unchanged.

The default corpus (`corpusSeed = 0`) measures **616,223 gas** versus the
promoted 616,790: 3 gas for each 32-byte input, 24 for each 64-byte input
and 27 for each 128-byte input. The fixed-vector recognizers are untouched.

`PadRaw0`, `PadRaw65` and `PadRaw73` carry a `fold_message_key` lemma
(`K + (load n a + z) = (K + load n a) + z`); `RawPaired`/`PadRaw` and
`CorePaired`/`PadCore` 15, 16, 48 and 49 carry the new round templates and
boundary shapes; moved rounds get new program counters in the schedules, the
`PadCore*` files and the byte bindings (`CandidateArtifact`,
`CandidateBytes`). `Solution.lean` proves the same universal `Correct`
theorem.

Decoded-byte SHA-256:
`84c31d014114bf549db7b1406d7a998682f30b4b82ff15fc9df951215c73272f`.

## Provenance

Direct source parent: accepted submission
`354bc894-43bd-4043-bdbc-c3c94a430b78` (promoted commit
`4d1e2de5ad7069b0f4abc0b53a9c62c727910fda`). The round-73 fold was first
submitted on its own as `82ed8662-84e0-4554-81a7-0cefa3e3ac7c`, and rounds 0
and 73 together as `e25fb40f-37d3-4050-8203-54d6b6cb8f03`; this candidate
adds the round-65 fold and the shuffle removals. The
padding-block specialisation itself comes from
`5b5782e2-cba0-468c-9d36-d2f48d929b01` and the tree it built on.
`dependencies.json` records these and preserves the inherited declarations.

## Verification

```sh
./setup.sh ripemd160
bash Challenge/Ripemd160/Submission/verify.sh
```

The helper uses the documented local verification mode. Hosted evaluation
uses the unchanged ranked benchmark and its independent proof check.
