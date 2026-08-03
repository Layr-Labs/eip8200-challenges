# MODEXP challenge: audit map

## Minimal specification

[`Spec.lean`](Spec.lean) defines the successful Osaka/EIP-7823 domain and the
single acceptance predicate `Correct`. The expected bytes are built from the
same padded EIP-198 parser, arbitrary-precision `modPow`, and fixed-width
encoder used by the pinned `Precompile.runModexp` semantics.

The three declared operand lengths must each be at most 1024 bytes. Oversized
tuples fail exceptionally under EIP-7823 and do not have a return value; the
reference executes `INVALID` for that separate failure domain.

## Reference artifact

[`Reference/reference.yul`](Reference/reference.yul) has a `MULMOD` fast path
for moduli up to 32 bytes and a 32-limb fallback for the complete 1024-byte
domain. [`Reference/reference.hex`](Reference/reference.hex) is the frozen
1,284-byte output of the pinned verified Yul compiler.

## Proof structure

[`ProofSupport/Bytecode.lean`](ProofSupport/Bytecode.lean) reduces the challenge
to `EvmProof.EventuallyEvaluates`. The direct proof is organized under
`Reference/Proofs/Bytecode/`; its execution and gas certificates target the
frozen byte array, not a compiler assumption.

## Falsification

```sh
lake exe modexpchallenge
```

The executable suite includes the canonical EIP-198 vectors, zero-length and
zero-modulus cases, missing trailing bytes, and a 257-bit modulus exercising
the multi-limb implementation. Tests are evidence, not the correctness proof.
