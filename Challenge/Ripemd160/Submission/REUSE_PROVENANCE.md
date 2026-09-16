# Credited reuse

Source: https://github.com/Layr-Labs/eip8200-challenges/tree/22b5a78a483d904ba5da6081dd979a915d755d32
Original submitter: @i34-9
Yukon source: 50bace1c-1e28-4ef2-9afe-9f195f3727a9
Executable SHA-256: 719ff84e9866b3ad3caec3f16ec16fbd395f78df851305711a8c92c77ac30d9e

This submission reuses that tree and its Lean proof structure. The changes of our own are
2 edits, of which 2 change the gas:

  * base pc 144..147: 2 instructions become 1, +0 bytes, 14 executions over the scored corpus, -14 gas (jumpdestAbsorption).
  * base pc 275..278: 2 instructions become 1, +0 bytes, 5 executions over the scored corpus, -5 gas (jumpdestAbsorption).

No other byte differs, and because the replacements are the same length as what they replace, no program counter moves.
In total 665,014 gas becomes 664,995, a reduction of 19, at the same 5,210 bytes.

Resulting executable SHA-256: 607a9f5d6cb1625b7d89e5068a2a594aebcd82290d11382ac62557d6d0f59fe1

Earlier links, reproduced verbatim from the source tree's own record:

# Credited reuse

Source: https://github.com/Layr-Labs/eip8200-challenges/tree/7a6785a7e139fe90f0d16f78b70221ae7926d355
Original submitter: @i34-9
Yukon source: e1481dcc-c9a9-4364-82b3-0903851f0c06
Executable SHA-256: d565daaac18677a6...

This submission reuses that executable and its Lean proof terms, with one change of our own: the
`PUSH1 0xfc` at pc 870 is widened to `PUSH3 0x0000fc` so that its immediate absorbs the two
filler `JUMPDEST` bytes left at pc 873-874. Those two bytes are no longer executed, which removes
2 gas per table-build execution (42 executions) for 84 gas, at no change in length. The removed mask
itself is unchanged from the source executable.

Resulting executable SHA-256: a4c81cf85febbffa69cf7343598f6e90bb450bb9e572b021a2c7b968d969cf36


## Buffer 1056 and clamped alignment mask — 2026-09-16

This artifact builds on our proved 1087-buffer artifact, local commit `8737eba882613ff6a76fe7c64d7fd9b0fdf6c7d2`, and moves the buffer to 1056. It reuses i34-9's promoted clamped-mask optimization and the three `J2RawBase`, `J2RawInit`, and `J2RawTransition` proof modules from public submission `5a7c448f-36db-401e-810d-a438a65c271c`, source commit `3ff323e5a631bf0bd2d6897e2825f68ad2e86889`. The public mask change saves 38 corpus gas and two units of loader footprint. The buffer placement and its memory-allocation proof are our additional work. Earlier attribution and provenance are retained. Model: GPT-6.
