# RIPEMD-160: early right-lane C-rotation, SWAP4 retired from the ordinary prologue (614,967 gas)

Parent: promoted commit `bb6842e9` (accepted `343b16c8`, 615,497 gas).

The right-lane prologue window (PC 794..977: `RawRight0`, `RawRight1`,
`RawPack`) runs once per compressed block (265 times on the corpus). Round 1
used to end with `DUP15 DUP7 MUL PUSH1 23 SHR` (rotated `C` for round 2) and
the pack window opened with `SWAP4` to exchange it with the round-0 `e` copy
left by a `DUP9`. Now round 0 computes the rotation directly in that slot
(`DUP11 DUP3 MUL PUSH1 23 SHR`, input `b` via the `rho[2]` alias), round 1
reads `e` from the suffix head (`DUP13`, alias `rho[0]`), the round-1 tail is
`PUSH4 K DUP13`, and the `SWAP4` disappears. +14 -14 -3 +1 (width pad) = -2
gas per block, 615,497 -> **614,967**.

Width: one `JUMPDEST` pad at PC 929 (before the 930 loop entry) keeps the
window at 183 bytes / 111 instructions; boundaries 794, 871, 930, 977 and all
later PCs and instruction indices are unchanged (round 0/1 split moves
830 -> 835).

Proof: stack at 977 (and `PrefixBefore.outputs` at 930) unchanged.
`RawRight0` slot 1, `RawRight1` input slot 1 / output slots 0 and 4 and a
new `rho[0]` alias, `RawPack.inputStack` order `a,k,b,c,d,e`; `CoreRight0`,
`CoreRight1`, `CorePack`, `CorePrologue` restated accordingly;
`PrefixBefore.template` = `FirstPrologue.before`; `CandidateArtifact`
parts 1/2, `CandidateBytes` chunks 12..14 and `bytecode.hex` carry the bytes.

---

# RIPEMD-160: PC-sourced 0x80 padding byte relocated beside a shifted 482 store in the first-block prologue (615,497 gas)

Parent: promoted commit `62e72056` (accepted `784a8fe6`, 615,508 gas).

The first-block table prologue (`PrepFirst0..5`, PC 9944..10184, 11 runs on
the corpus) wrote the 0x80 padding marker at 787 with
`PUSH1 128 PUSH2 787 MSTORE8` in `First1`, and in `First3` stored the word
read from 262 at 468 with its high 14 bytes cleared by
`DUP3 PUSH18 (2^144-1) AND PUSH2 468 MSTORE`.

`First3` now stores `x << 112` at 482 (`DUP3 PUSH1 112 SHL PUSH12 482 MSTORE`):
the same 18 low bytes land at 482..499; 468..481 keep their entry zeros and
the 14 zero bytes go to 500..513, which are zero at that point in the
first-block layout. That shortens the window by 17 bytes, which hosts the
padding byte as `PC PUSH4 787 MSTORE8` with the `PC` byte at exactly 10112
(10112 mod 256 = 0x80). `First1` drops its `MSTORE8` and widens the 216
literal from `PUSH16` to `PUSH22`, so every window keeps its byte range and
no PC moves. 787 is touched by no other first-path store or load, so moving
the byte write from step 6 to step 17 leaves `symbols27` unchanged
(`FirstMemory.memory6` is now the identity step; `memory17` writes both
stores; `FirstLayout.shl112_byte` gives the byte view of the shift).

Instruction count unchanged (-3 in `First1`, +3 in `First3`); byte-diversity
budget 15,063 -> 15,062 (limit 15,066).

Gas: `PC` (2) replaces `PUSH1 128` (3), `SHL` replaces `AND`: -1 per
first-block prologue, 11 executions: 615,508 -> **615,497**.

---
