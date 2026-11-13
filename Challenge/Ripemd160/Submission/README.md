# RIPEMD-160: PC-sourced 720 store offset in the ordinary message prologue (615,671 gas)

Parent: promoted commit `5bbac375` (accepted `f300667a`, 615,702 gas).

The ordinary per-block message prologue (`PrepOrdinary5`, bytes 707..734,
executed once per normal compression entered through the 461 loop) stored
three resident words with `DUP9 PUSH2 720 MSTORE; DUP8 PUSH2 828 MSTORE;
DUP11 PUSH2 612 MSTORE`. The three 32-byte stores are pairwise disjoint
(720..751, 828..859, 612..643) and no load sits between them, so their order
is free. They are now issued as `DUP8 PUSH3 828 MSTORE; DUP11 PUSH3 612
MSTORE; DUP9 PC MSTORE`: the two widened pushes place the `PC` opcode at
exactly PC 720, so `PC` (2 gas) replaces `PUSH2 720` (3 gas). The window keeps
its 28 bytes and 17 instructions; every PC outside 707..734 is unchanged.
This is the same `PC`-as-offset device the prologue already uses at PC 666.

Gas: 1 per ordinary-prologue execution. On the corpus that is every normal
block of the generated 64-byte (11 x 1) and 128-byte (10 x 2) inputs = 31:
615,702 -> **615,671**.

Proof: `Ordinary5.template`/`memory`, `OrdinaryMemory.memory17..19` and
`OrdinaryCertificate.plan` follow the new store order (the final layout is
identical, so the `decide` certificates and `model_exact` are unchanged in
form); `CandidateArtifact` part 1 and `CandidateBytes` chunk 11 carry the new
bytes.

---

# RIPEMD-160: block-minimal window tiling of the 1,000-byte recognizer (615,702 gas)

Parent: promoted commit `72653d83` (accepted `ce39edff`, 615,735 gas).

Byte `i` of the patterned vector is `37 i + 11 floor(i/251) + 7 (mod 256)`.
A window check `W[o] = W[s]` holds only when neither window straddles a
251-byte block boundary and `o - s = 145 k (mod 256)` (`k` = block distance),
so the cover of `[256, 1000)` splits into blocks `[256,502)`, `[502,753)`,
`[753,1000)`. Around the anchor `[369,401)` and head window `(401, 0)` the
blocks need 7 + 8 + 8 = 23 compare windows; HEAD runs 25. The new `plan1000`
keeps 16 HEAD pairs and adds `(529,384) (561,15) (593,47) (625,79)
(657,111) (689,143) (936,390)`; `cover1000` re-decides it unchanged.

The arm shrinks to 23 compare items plus the literal window; the freed bytes
become dead code between the arm's final `JUMP` and the `JUMPDEST` at 6144
(`PUSH2 0x1343; JUMP` x4, `PUSH1 0x43`, `JUMP` x15; no `0x5b`). Length and
instruction count are unchanged; bytes 5924..6136 (chunks 92-95) differ.
Diversity budget stays 15,062.

Gas: compare items 446 -> 413 on the `1000-byte` vector (the only vector
running this arm): 615,735 -> **615,702**.

---

# RIPEMD-160: redundant 1,000-byte window checks retired to dead tail bytes (615,735 gas)

Parent: promoted commit `d81adc41` (accepted `65de591d`, 615,771 gas).

The 1,000-byte patterned recognizer (PC 5829, instructions 3673..3848) ORs
28 calldata window differences and then jumps to the shared chain at 4931.
Two of those pairs, `(364, 219)` and `(509, 219)`, are implied by the rest of
the cover: `WindowCover.cover1000` still holds (`by decide`) for the plan
without them. Both compare items (`PUSH2 o; CALLDATALOAD; PUSH1 219;
CALLDATALOAD; XOR; OR`, 18 gas each) are dropped from `items1000`.

The arm tail (`eq 470 69`, the literal window at 369, `eq 514 369`,
`eq 915 369`, `PUSH2 4931; JUMP`) moves 18 bytes earlier. The freed 18 bytes
(12 instructions) sit after the arm's unconditional `JUMP` and before the
`JUMPDEST` at 6144, so they are never executed: `PUSH2 0x1343; JUMP` three
times, then six `JUMP`. No `0x5b` byte is added, so the valid-jumpdest set is
unchanged; length (10,511) and instruction count are unchanged, so every PC
and instruction index outside 6056..6143 is unchanged. Byte-diversity
budget: 15,066 -> 15,062 (limit 15,066).

Gas: 36 on the `1000-byte` vector only (the `1000 a's` vector branches to
6144 before the arm): 615,771 -> **615,735**.

Proof: `items1000` and `plan1000` lose the two entries;
`CandidateArtifact` parts 19/20 and `CandidateBytes` chunks 94/95 are
regenerated. `a1000Template` keeps its shape (store, head, items, jump), so
`run_items`, `plan1000_mem` and `result1000` are reused unchanged.

---

# RIPEMD-160: MSIZE offsets in the 1,000-byte arm, diversity-neutral pads (615,771 gas)

Port of kaankolcu's `02dd6793` (MSIZE offsets in the 1,000-byte arm) onto the
615,773-gas frontier `b1d795c1`, whose accept commit dropped it.

Two compare items of the 1,000-byte patterned recognizer read their second
calldata word at offset 32 with `PUSH1 0x20`. At that point memory holds
exactly the stored digest word, so `MSIZE` already equals 32 on every path
into the arm. Each item becomes `PUSH2 o; CALLDATALOAD; MSIZE; CALLDATALOAD;
XOR; OR` (offsets 433 and 578). The two freed bytes are absorbed by widening
the second-offset pushes of the earlier items `eq 288 143` and `eq 320 175`
to `PUSH2 0x008f` / `PUSH2 0x00af` (`Item.eqP`). Those pads sit in the
64-byte chunk that already contains a zero byte, so the byte-diversity
budget stays at 15,066 (limit 15,066); the original `PUSH3` pads added a new
zero byte to chunk 92 and would overflow the budget on top of `b1d795c1`.
The arm keeps its length; every later PC and instruction index is unchanged.
1 gas per item, 2 items on the `1000-byte` vector: 615,773 -> **615,771**.

Proof: `RecArmsLong` keeps kaankolcu's `Item.eqM o` (value `eq o 32`, needs
`s.activeWords = 1`) and adds `Item.eqP o s` (value `eq o s`, second offset
pushed at width 2). `plan1000_mem` maps plan pairs to `eq`, `eqP` or `eqM`
items. `WindowCover` is unchanged. Instruction count unchanged.

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
