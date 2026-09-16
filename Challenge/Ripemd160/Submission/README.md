# RIPEMD-160: reuse consumed input memory

This artifact reduces the seed-zero corpus cost from 667,020 to **666,935 gas**.
It contains 5,224 bytes: 4,944 executable bytes and the inherited 280-byte digest
table, with 3,720 executable instructions.

SHA-256: `e4db447a28084afefb4fca6954735b0717e38a1df062e4868f6602eb4ac0c8c2`.

The parent is our promoted submission `eea7422c-fa6f-48e3-9923-63c2b97159e8`
(server source `d7019813cd954d43b28f0872e91776896476ce0d`). It inherits the
public RIPEMD work of i34-9, ercumentyildirim, and earlier contributors.

The input buffer moves from address 1120 to 1087. Both words of the current
64-byte block are loaded before the schedule overwrites memory through byte
1111. The next input block starts at 1151 or later, so the overwritten bytes
have already been consumed. This reduces the memory expansion charge by one
word for the generated 32-, 64-, and 128-byte inputs.

The exact-32 path formerly used MSIZE=1152 to supply the padding byte 0x80.
It now uses PUSH1 128. Narrowing the following PUSH2 99 to PUSH1 99 preserves
all subsequent PCs. Instruction 216 alone moves from PC 324 to PC 325.
Five PUSH2 operands relocate the input copy, its two load pointers, sentinel,
and footer. The 32-byte route saves 2 gas per input; 64- and 128-byte routes
save 3 gas per input. The scored corpus improvement is 11*2 + 11*3 + 10*3 = 85.

The proof context tracks the first unprocessed block. A schedule step preserves
all later message blocks while allowing already consumed bytes to change.
The allocation lemmas use a ceiling for the unaligned input pointer. The
padding marker has an ordinary literal-push step proof.

Validation completed: all 120 local corpus seeds, 2,500 fuzz inputs, exact
assembly, runtime jumps, CODECOPY bounds, and the original read-only artifact
loader (sum 7538). The full Lean build passed all 3,720 jobs. The final candidate
uses only `propext`, `Classical.choice`, and `Quot.sound`. The protected benchmark
must additionally pass on these exact bytes before this artifact is submitted;
its result is recorded in the submission note.
