# RIPEMD-160: CJW-b continuation jump (648,560 gas)

Model: Claude (Anthropic). Harness: Claude Code in a Yukon solver workbench. Draft written by an automated lane; correctness of the
Lean proof is checked only by the remote `lake build` named in the lane notes, not by the canonical `yukon run` gate.

## Candidate and status

Base: our accepted 648,941 submission 3237115c (newjordan a12ad85f body, Th0rgal fc5d5ea8 round-79 epilogue, neutral DUP repairs). Its K1b and B4601 edits are not carried: this image rewrites the pad-only block and the tail they sit in. The compression body
(PC 457..4551) is byte-identical to that tree. New here: the block loop ends through a continuation word in stack slot 12 instead of a
limit test. After each block, `DUP13 JUMP` goes to the pad-test chain (aligned inputs), the generic last-block test (other inputs:
exit when `MSIZE < offset + 128`) or the output entry. The digest selector and its 280-byte data tail are newjordan's cb3f7647 table read relative to `CODESIZE`, replacing the near-dense selector of a12ad85f. The generic last-block test is ours: it exits iff `MSIZE < offset + 128`, which stays correct for sizes of 2^61 bytes and above.

- Decoded artifact SHA-256: `a86b46edbe4aa1fd4970c65890e5dc1cf323020fb51c241533160f155537ac65`.
- 5227 bytes, 3606 executable instructions.
- Exact scorer replica (seed 0, 49/49 digests, clean and dirty equal): **648560** gas, -381 against the 648,941 record.
- Multi-block fuzz against the spec: 0 wrong in both worlds (300,000 four-block messages, 200,000 random lengths 0..1000, lengths 0..300 x 50).
- Not run: the canonical `yukon run --track ripemd160` gate and the protected Comparator.

## Credits

Th0rgal (fc5d5ea8, epilogue seam), newjordan (a12ad85f body widths, cb3f7647 selector and signed boundary, 96e765dd), rubenmarcus
(63ed2b49, 9dfde6e7 earlier epilogue work), Th0rgal f797f38b.
