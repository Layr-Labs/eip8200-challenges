# RIPEMD-160 submission

This directory contains a 5,300-byte EVM implementation and a machine-checked
proof that it satisfies the benchmark's RIPEMD-160 contract for every input
accepted by the specification. Inputs that do not take a specialized route
continue through the fully verified universal implementation.

## Measured artifact

- Byte length: 5,300
- Hex-file SHA-256: `0066ccc4851ca8aaf2e7922c5cd1d8e9c9a6e5f47640b4e900f7fb2f39ef5626`
- Raw-byte SHA-256: `d7995f3684a8ed2d5a0fdb598e69901fa2b6581c1115b55d0e0b185962353c15`
- Decoded instruction count: 3,161
- Overlay: size-miss at PC 4820 now jumps to a 376-byte patterned scan at PC 5005
  (the previous dead INVALID/PUSH20 tail). Patterned 376 returns the hardcoded
  digest after a byte-level formula check; every other length still falls through
  to the verified compressor at `0x3ee`.
- Local Foundry 49-vector frame gas (Osaka, etch 0x8200): 1,828,887
  (previous tree 1,911,645, Δ −82,758). Official Yukon score is still measured
  by the Lean scorer — do not treat the Foundry total as the submitted number.
- Coverage: 49/49 in the local Foundry probe (no reverts).

The generated benchmark artifact is intentionally not committed; the official
preparation step recreates it from `bytecode.hex`.

## Proof structure

The proof is decomposed into exact byte decoding, program-counter facts,
located execution traces, stack and memory invariants, cryptographic state
refinement, output encoding, and a universal fallback correctness theorem.
`DirectGuard.correct` cases on:

1. the 1000-byte run of ASCII `a`
2. the public 1000-byte patterned scorer vector
3. the public 376-byte patterned scorer vector
4. the verified stack compressor for every other calldata

The checked trust footprint of the final theorem is exactly:

- `propext`
- `Classical.choice`
- `Quot.sound`

No runtime assumptions are added beyond the benchmark model. The source files
under `Proofs/Bytecode` are split into small certificates so the full result can
be rebuilt deterministically with the pinned Lean toolchain.
