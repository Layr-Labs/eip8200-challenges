# RIPEMD-160: fold the padding block's round-73 message word into its key

In the constant padding block that follows every exact 64·k-byte message, the
message words are compile-time constants. In left/right paired round 73 of that
padding compressor the candidate folds the paired message word (previously read
from the stack with `DUP12` and added with `ADD`) into the round's pushed key
literal. The key push keeps its 19-byte width, and the following shift-count
push becomes `PUSH3 0x000014` instead of `PUSH1 0x14`, so the routine keeps its
length: every later program counter and jump destination is unchanged and the
bytecode stays at 10,511 bytes.

Old bytes at 9689–9716: `PUSH19 K; ADD; ADD; DUP12; ADD; DUP7; AND; MULMOD; PUSH1 0x14`.
New bytes: `PUSH19 (K + W); ADD; ADD; DUP7; AND; MULMOD; PUSH3 0x14`.

`PadRaw73.fold_message_key` proves `K + (load n 540 + z) = (K + W) + z` for the
constant padding word, and `PadRaw73.actualOutput_eq` rewrites the generated
stack with it; the remaining padding-compressor, padding-site, artifact and
control proofs are re-pinned to the new bytes. `Solution.lean` retains the same
universal `Correct` theorem.

The padding block runs once for each generated 64-byte and 128-byte input, so
the default corpus (`corpusSeed = 0`) measures **616,664 gas** versus the
inherited 616,790 baseline: six gas saved for each of the 21 generated 64- and
128-byte inputs (two instructions, 3 gas each). Fixed-vector recognizers and the
32-byte path are untouched.

Decoded-byte SHA-256:
`fbcd586db2d6129a49d5b5d65272f696b90a1e8730f71d01cb5c447df7934450`.

## Provenance

The direct source parent is accepted submission
`354bc894-43bd-4043-bdbc-c3c94a430b78` (promoted commit
`4d1e2de5ad7069b0f4abc0b53a9c62c727910fda`), whose tree, proofs and all other
optimizations are retained unchanged. Folding known padding words into round
keys follows the technique of the padding-specialized frontier introduced in
`5b5782e2-cba0-468c-9d36-d2f48d929b01` (recorded in `dependencies.json`); this candidate applies it to a round where the
word was still added from the stack.

## Verification

From the repository root, use the pinned toolchain and unchanged benchmark:

```sh
./setup.sh ripemd160
bash Challenge/Ripemd160/Submission/verify.sh
```

The helper uses the documented local verification mode. Hosted evaluation
uses the unchanged ranked benchmark and its independent proof check.
