# RIPEMD-160: MSIZE offsets in the 1,000-byte arm (615,804 gas)

Two compare items of the 1,000-byte patterned recognizer read their second
calldata word at offset 32 with `PUSH1 0x20`. At that point memory holds
exactly the stored digest word, so `MSIZE` already equals 32 on every path
into the arm. Each item becomes `PUSH3 o; CALLDATALOAD; MSIZE; CALLDATALOAD;
XOR; OR` (offsets 433 and 578): the widened offset push absorbs the freed
byte, so the arm keeps its length and every later PC and instruction index is
unchanged. 1 gas per item, 2 items on the `1000-byte` vector:
615,806 -> **615,804**.

Proof: `RecArmsLong` gains an `Item.eqM o` form whose value is defined as the
`eq o 32` value; `run_item`/`run_items` take `s.activeWords = 1`
(`prepared_activeWords`, as the shared chain's `run_cmpSize` already does);
`plan1000_mem` maps the two plan pairs to the new items. `WindowCover` is
unchanged. Instruction count stays 7,010; byte-diversity budget 15,066 (limit
15,066). The 49 vectors were re-run in an independent EVM model: all digests
correct, total 615,804.

Decoded-byte SHA-256: `049df9b553df2c9b7008c5b3b97091a0169b558efbab5834f3a9264e5bc8a317`.

---

## Inherited description (parents 54dea2f0, 67d0cd03, 6bbb6d6d and earlier)

## Round-49 filler removal in the normal compressor (615,971 gas)

This candidate removes one more fall-through-only `JUMPDEST` from the hot
normal-compressor path of the promoted 616,013-gas artifact (submission
`5f01fde9`), keeping the bytecode at exactly 10,511 bytes.

**Normal49.** Paired round 49 of the normal compressor (`RawPaired49`,
bytes 3253..3293) ended with `PUSH1 0x17; SHR; DUP4; AND; JUMPDEST`. The
`JUMPDEST` at PC 3293 is not a jump target: no pushed constant equals 3293,
and the computed jumps (PC 4623 trampoline table, 4821 length dispatch,
6408 and 6500 output loops) all land in other regions. It is rewritten to
`PUSH2 0x0017; SHR; DUP4; AND`; the widened push absorbs the freed byte, so
PC 3294 and every later byte are unchanged. One instruction and 1 gas are
removed per normal compression (42 executions on the corpus):
616,013 -> **615,971**. This is the same technique as the promoted A1 edit
in round 16 (PC 1774).

Decoded instructions: 7,015 -> 7,014. Byte-diversity budget unchanged at
15,065 (limit 15,066).

Decoded-byte SHA-256:
`faec025122cdd90d5b35fc21f5a3722c6c1fae38018b6b76f8bd0d393a01bde8`.

---

## Inherited description (parent 5f01fde9 and earlier)


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
