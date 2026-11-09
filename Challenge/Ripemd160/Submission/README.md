# RIPEMD-160: fold padding words into the round keys of padding rounds 0 and 73

Every input whose length is a multiple of 64 bytes ends with a constant padding
block, compressed by a specialised routine whose message words are literals.
In paired rounds 0 and 73 of that routine a non-zero padding word was still
added in its own step (`PUSH word; ADD; DUPn; ADD`, with the round key copied
from the stack). The candidate pushes the precomputed `key + word` instead, so
each of the two rounds loses one `DUP` and one `ADD` (6 gas). Round 43's
`PUSH13` literal is widened to `PUSH14` with a leading zero byte (same 3 gas),
so the routine keeps its length: every program counter from byte 9,729 on,
including the 32-byte path and the code-copied table data, is unchanged, and
the bytecode stays at 10,511 bytes.

`PadRaw0.fold_message_key` and `PadRaw73.fold_message_key` prove
`K + (load n a + z) = (K + load n a) + z` for the constant padding words, and
the round specifications consumed by `PadCore*` are unchanged. The rounds that
moved get new program counters in `PadSchedule`, `PadCore*`, `PadSites` and the
byte bindings (`CandidateArtifact`, `CandidateBytes`). `Solution.lean` proves
the same universal `Correct` theorem.

The padding block runs once for each generated 64-byte and 128-byte input, so
the default corpus (`corpusSeed = 0`) measures **616,538 gas** versus the
promoted 616,790: twelve gas saved for each of those 21 inputs. The 32-byte
path and the fixed-vector recognizers are untouched.

Layout note: the protected generated `Benchmark/Artifact.lean` only compiles
while the sum over its 64-byte chunks of distinct byte values stays at or
below 4,555 for this code length; this layout has exactly 4555.

Decoded-byte SHA-256:
`efafd8808e6096a88d24d748552d3ac6b5c1c4d2487dce484a916bd686220969`.

## Provenance

Direct source parent: accepted submission
`354bc894-43bd-4043-bdbc-c3c94a430b78` (promoted commit
`4d1e2de5ad7069b0f4abc0b53a9c62c727910fda`). The round-73 fold was first
submitted on its own as `82ed8662-84e0-4554-81a7-0cefa3e3ac7c`; this candidate
adds the round-0 fold. The padding-block specialisation itself comes from
`5b5782e2-cba0-468c-9d36-d2f48d929b01` and the tree it built on.
`dependencies.json` records these and preserves the inherited declarations.

## Verification

```sh
./setup.sh ripemd160
bash Challenge/Ripemd160/Submission/verify.sh
```

The helper uses the documented local verification mode. Hosted evaluation
uses the unchanged ranked benchmark and its independent proof check.
