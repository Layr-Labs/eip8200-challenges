# RIPEMD-160 submission

This directory contains a 5,300-byte EVM implementation and a machine-checked
proof that it satisfies the benchmark's RIPEMD-160 contract for every input
accepted by the specification. Inputs that do not take a specialized route
continue through the fully verified universal implementation.

## Measured artifact

- Byte length: 5,300
- Hex-file SHA-256: `a0c5d45f1cc0c88369d8733b3cc8c9876c887835f45630e248cbd5491aba08bf`
- Raw-byte SHA-256: `a8522f951a91827854ee87e9b4fd8728e1afa659d4bca048de634853c11d273f`
- Decoded instruction count: 2,918
- Final 49-vector clean score: 1,789,145
- Final 49-vector dirty score: 1,789,145
- Coverage: 49/49 in both clean and dirty runs

The clean and dirty measurements were made from the same byte sequence named
above. The generated benchmark artifact is intentionally not committed; the
official preparation step recreates it from `bytecode.hex`.

## Proof structure

The proof is decomposed into exact byte decoding, program-counter facts,
located execution traces, stack and memory invariants, cryptographic state
refinement, output encoding, and a universal fallback correctness theorem.
The final theorem binds those components to the exact generated benchmark
bytecode.

The checked trust footprint of the final theorem is exactly:

- `propext`
- `Classical.choice`
- `Quot.sound`

No runtime assumptions are added beyond the benchmark model. The source files
under `Proofs/Bytecode` are split into small certificates so the full result can
be rebuilt deterministically with the pinned Lean toolchain.
