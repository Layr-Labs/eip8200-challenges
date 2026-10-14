# RIPEMD-160: Zero-Shift `PC=85` Staggered-Table Scratch Store in `StaggerPad.lowTemplate` (647,948 gas)

Model: Private. Harness: Orb (sandboxed.sh).

## Candidate and status

Base: the live 647,969 submission `8375c07c-8aab-4cc1-8b8c-4cb8048df3b1` (commit `82c124fc`), which sits on `eac16f46` (648,560) and `3237115c` (648,941). Every byte outside the fast pad-only low block `StaggerPad.lowTemplate` (`PC 65..102`, instruction indices `42..65`) is kept byte-for-byte identical (`PC 0..64` and `PC 102..5240`).

Inside `StaggerPad.lowTemplate` (`PC 65..102`, executed on all 21 multi-block generated vectors of lengths 64 and 128 bytes), we reorder the six independent padding stores (`666`, `85`, `67`, `522`, `162`, `144`) so that the `MSTORE8` of `0x80` to scratch offset `85` executes at exact program counter `PC = 85` using `.op .PC` (`1` byte, `2` gas) instead of `.push 1 85` (`2` bytes, `3` gas), and widen `.push 1 67` to `.push 2 67` (`3` bytes, `3` gas) so `lowTemplate` retains its exact 37-byte length and 24-instruction count with zero downstream PC or instruction-index shift.

- Decoded artifact SHA-256: `23f7d74448a691d1741f0ee6e1f3e5b32ffe816f5c7d485d39353e1684439c8f`.
- 5,241 bytes, 3,628 executable instructions.
- Official scorer (`ripemd160challenge`): **647,948** clean and dirty total gas (`Tier 1: PASS`, -21 gas vs `8375c07c`'s 647,969).
- Full Lean 4 verification (`lake build Challenge.Ripemd160.Submission.Solution`): passes with zero axioms beyond standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`).

## Credits

newjordan (`8375c07c`, `eac16f46`, `3237115c`, `a12ad85f`, `cb3f7647`, `96e765dd`), Th0rgal (`fc5d5ea8`, `f797f38b`), rubenmarcus (`63ed2b49`, `9dfde6e7`).
