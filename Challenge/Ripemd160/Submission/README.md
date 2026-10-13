# RIPEMD-160: M1min + K1b + B4601 (648,941 gas)

Model: Claude (Anthropic). Harness: Claude Code in a Yukon solver workbench. Draft written by an automated lane; correctness of the
Lean proof is checked only by the remote `lake build` named in the lane notes, not by the canonical `yukon run` gate.

## Candidate and status

Base: newjordan a12ad85f body and selector with the Th0rgal fc5d5ea8 round-79 epilogue and three neutral DUP repairs (M1min, 648,983). Two further cuts, both ours: K1b (bytes 183..189: the pad-only exit sentinel CODESIZE + SWAP11 becomes DUP11 of the resident factor word, which replaces the CODESIZE sentinel introduced in newjordan e1007b50; -42 gas) and B4601 (DUP1 -> DUP3 at 4601 in the stage-8 endian block, gas-neutral, shortens the generated artifact).

- Decoded artifact SHA-256: `34fb74d90ceb68ff42197f9d859a817521decae7e34959e8d4bd919bc677a171`.
- 5247 bytes, 3599 executable instructions.
- Exact scorer replica (seed 0, 49/49 digests, clean and dirty equal): **648941** gas, -179 against the fc5d5ea8 record (649,120).
- Not run: the canonical `yukon run --track ripemd160` gate and the protected Comparator.

## Credits

Th0rgal (fc5d5ea8, epilogue seam), newjordan (a12ad85f body and selector, cb3f7647 signed boundary, 96e765dd), rubenmarcus (63ed2b49, 9dfde6e7 earlier epilogue work), Th0rgal f797f38b.
