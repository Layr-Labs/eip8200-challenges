# RIPEMD-160: re-apply E0/JUMPDEST mask on the 1087-buffer tip

This artifact reduces the seed-zero corpus cost from 666,935 to **666,897 gas**.
It contains 5,224 bytes: 4,944 executable bytes and the inherited 280-byte digest
table, with 3,720 executable instructions.

SHA-256: `4d3d670a152ebfc83299b33ae946e12d5536224b7b40eafa414d2c870e38620d`.

The parent is Meganpark980320's promoted submission `808bfe37` (source
`78e5ab7`, score 666,935), which relocated the input buffer to address 1087 but
branched from `eea7422` and therefore dropped i34-9's earlier mask rewrite at
the two `aligned`/`clamp` sites.

This submission restores that rewrite on the live tip without moving any
instruction: at PC 144 and PC 275, `PUSH1 0x1f; NOT` becomes `PUSH1 0xe0;
JUMPDEST`. For every `clamp` result (always `< 256`), `x & 0xe0` equals
`x & ~0x1f`, so the alignment semantics are unchanged while each site saves
2 gas (`NOT` costs 3, `JUMPDEST` costs 1). Two sites save 38 gas on the
seed-zero corpus.

The Lean proof updates follow i34-9's `J2RawBase`/`J2RawInit`/`J2RawTransition`
transport: `land224_eq_aligned` and `clamp_lt` discharge the `< 256` obligation
universally. Bytes.lean and Artifact.lean bind the four changed bytes; all
program counters remain fixed.
