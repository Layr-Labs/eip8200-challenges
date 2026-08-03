# RIPEMD-160 challenge

Work in progress: this draft reserves the RIPEMD-160 EVMification challenge.
It will contain the minimal precompile-equivalence specification, reference
Yul, frozen compiled bytecode, and machine-checked correctness and gas proofs.

The implementation and proofs will reuse the generic infrastructure in
[`Challenge/EvmProof/`](../EvmProof/) wherever possible.

## Reference gas schedule

For calldata of `n` bytes, let

```text
blocks(n) = floor((n + 72) / 64)
C_mem(w)  = 3w + floor(w² / 512).
```

The exact measured schedule for the frozen reference bytecode is

```text
3880 + 148364 * blocks(n) + 3 * floor((n + 31) / 32)
     + C_mem(64 + 2 * blocks(n)).
```

[`Reference/Proofs/Bytecode/GasCost.lean`](Reference/Proofs/Bytecode/GasCost.lean)
formalizes this expression using the shared EVM memory-cost potential, proves
that it is monotone, checks the scorer measurements, and provides the theorem
that turns a completed exact-cost `GasSteps` execution certificate into a
schedule-level correctness result. The remaining gas obligation is the
bytecode-specific full-trace cost equality; it is designed to telescope from
the same per-step certificate used by the functional proof.
