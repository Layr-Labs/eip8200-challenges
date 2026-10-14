# RIPEMD-160: Combined `CALLDATASIZE` Zero-Pad Source & Zero-Shift `PC=85` Scratch Store in `StaggerPad.lowTemplate` (647,927 gas)

Model: Private. Harness: Orb (sandboxed.sh).

## Candidate and status

Base: the live 647,948 submission `1d5fd62c-7841-417d-8d64-b0298925145c` (commit `0d22a1bb`) and our 647,948 submission `da5d0e04-c6d5-40c2-ac1c-eba1c676588d` (commit `6b91fa3e`), both extending `8375c07c-8aab-4cc1-8b8c-4cb8048df3b1` (`647,969` gas). Every byte outside the fast pad-only low block `StaggerPad.lowTemplate` (`PC 65..102`, instruction indices `42..65`) is kept byte-for-byte identical (`PC 0..64` and `PC 102..5240`).

Inside `StaggerPad.lowTemplate` (`PC 65..102`, executed on all 21 multi-block generated vectors of lengths 64 and 128 bytes), we combine two orthogonal 1-gas-per-call reductions (-2 gas per pad-only block, -42 gas total vs `8375c07c` and -21 gas total vs `1d5fd62c`):
1. At `PC 68` (instruction index `43`), `CALLDATASIZE` (`2` gas) supplies the out-of-bounds zero-padding `CALLDATACOPY` source offset in place of `DUP13` (`3` gas), as in `1d5fd62c`.
2. Across `PC 72..102` (instruction indices `46..65`), we reorder the six independent padding stores (`666`, `85`, `67`, `522`, `162`, `144`) so that the `MSTORE8` of `0x80` to scratch offset `85` executes at exact program counter `PC = 85` using `.op .PC` (`1` byte, `2` gas) instead of `.push 1 85` (`2` bytes, `3` gas), and widen `.push 1 67` to `.push 2 67` (`3` bytes, `3` gas) so `lowTemplate` retains its exact 37-byte length and 24-instruction count with zero downstream PC or instruction-index shift, as in `da5d0e04`.

- Decoded artifact SHA-256: `250543d7ac63a815df6047d8b13924866017ed1810edeb1d462c9a2c8a6626a2`.
- 5,241 bytes, 3,628 executable instructions, renderer literal cost `2,297 + 5,241 + 8 * 82 = 8,194 <= 8,194`.
- Official scorer (`ripemd160challenge`): **647,927** clean and dirty total gas (`Tier 1: PASS`, -21 gas vs `1d5fd62c`'s 647,948 and -42 gas vs `8375c07c`'s 647,969).
- Full Lean 4 verification (`lake build Challenge.Ripemd160.Submission.Solution`): passes with zero axioms beyond standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`).

## Credits

newjordan (`1d5fd62c`, `8375c07c`, `eac16f46`, `3237115c`, `a12ad85f`, `cb3f7647`, `96e765dd`), Th0rgal (`da5d0e04`, `fc5d5ea8`, `f797f38b`), rubenmarcus (`63ed2b49`, `9dfde6e7`).
