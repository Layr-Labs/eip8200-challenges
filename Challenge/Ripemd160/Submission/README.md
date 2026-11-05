# RIPEMD-160: direct calldata read on the current proof frontier

This candidate replaces `DUP12; MLOAD` at byte offsets 9912–9913 with
`PUSH0; CALLDATALOAD` on the arbitrary 32-byte-input path. Both sequences
have two instructions and two bytes, so every subsequent program counter
and jump destination remains unchanged. Bytecode stays at 10,511 bytes.

The original memory word is the 32-byte calldata previously copied to 1056.
`FirstComplete.load_eq` proves the equality, and both entry callers discharge
it. `FirstRead.run` proves execution of the new instructions; the existing
compression, padding and serialization proofs then compose unchanged.
`Solution.lean` retains the same universal `Correct` theorem.

Matched protected-scorer execution gives 616,790 gas versus the inherited
616,801 baseline: one gas saved for each of the eleven generated 32-byte
inputs. All 98 clean/dirty checks pass. A separate 64-input differential
check reports no digest failures or gas regressions; the 32 arbitrary
32-byte cases each save one gas. These measurements are not official
Yukon acceptance. Full Linux ranked Comparator verification passed on
2026-11-05: the independent Lean kernel accepted the solution, the process
exited normally with status 0, and the protected scorer returned 616,790 gas.

Decoded-byte SHA-256:
`29561ab2b5c3ee546e4645c92896a285a3314f7a6b319bc4ed819b0114f22eab`.

## Provenance

The direct source parent is accepted submission
`3b458b01-80a9-45c7-86bc-caa2e1a60bfd`, as present in source commit
`97f6c711f9cd7a9675c51441dcd704e2c610253b`.
The calldata-load technique and local execution/equality proofs are adapted
from published submission `083515e7-2ccd-462b-8c38-59f0e4ecf57d`
(commit `a5a1910a88192b1e5c91b09c71eccad0fbf3f2cf`). That earlier candidate
was rejected on score against its contemporary frontier. This candidate
ports the technique to the later table/compressor frontier, retaining its
current addresses, code-aware memory proof and all other optimizations.

`dependencies.json` records both sources and preserves the inherited
proof-tree dependency declarations. The inherited Apache 2.0 license and
notices apply.

## Verification

From the repository root, use the pinned toolchain and unchanged benchmark:

```sh
./setup.sh ripemd160
bash Challenge/Ripemd160/Submission/verify.sh
```

The helper uses the documented local verification mode. Hosted evaluation
uses the unchanged ranked benchmark and its independent proof check.
