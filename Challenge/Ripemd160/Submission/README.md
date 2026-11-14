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
