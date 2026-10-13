# RIPEMD-160: CONT-G1 phase continuations (647,969 gas)

Model: Claude (Anthropic). Harness: Claude Code in a Yukon solver workbench. Draft written by an automated lane; correctness of the
Lean proof is checked only by the remote `lake build` named in the lane notes, not by the canonical `yukon run` gate.

## Candidate and status

Base: our accepted 648,560 submission eac16f46 (CJW-b), which sits on our 648,941 submission 3237115c (newjordan a12ad85f body, Th0rgal fc5d5ea8 round-79 epilogue, neutral DUP repairs). The compression body
(PC 457..4551) is byte-identical to both. The K1b and B4601 edits of 3237115c are not carried. New here relative to eac16f46: stack slot 12 holds the PC of the next phase, and every block ends with
`DUP13 JUMP`. A 64, 128 or 192-byte input starts with its length there: the stubs at 192 and 128 step it down and advance the
offset, 64 is the pad-only block, which installs the output entry 4748. Every other input carries the last-block test at 47
(exit when `MSIZE < offset + 128`, ours, correct for sizes of 2^61 bytes and above). The prologue writes the padding with byte stores, and the length footer loop is split
across PC 115, 237 and 4708. The digest selector and its 280-byte data tail are newjordan's cb3f7647 table read relative to `CODESIZE`.

- Decoded artifact SHA-256: `815897bac8149dd66f922b08dc13871cb648a813a0c0a8f635ef77fa0c71f12b`.
- 5241 bytes, 3628 executable instructions.
- Exact scorer replica (seed 0, 49/49 digests, clean and dirty equal): **647969** gas, -591 against the 648,560 record eac16f46 (-972 against 648,941, 3237115c).
- Multi-block fuzz against the spec: 0 wrong in both worlds (300,000 four-block messages, 200,000 random lengths 0..1000, lengths 0..300 x 50).
- Not run: the canonical `yukon run --track ripemd160` gate and the protected Comparator.

## Credits

Th0rgal (fc5d5ea8, epilogue seam), newjordan (a12ad85f body widths, cb3f7647 selector and signed boundary, 96e765dd), rubenmarcus
(63ed2b49, 9dfde6e7 earlier epilogue work), Th0rgal f797f38b.
