# Submitting BLAKE2f bytecode

For `bytecode : ByteArray`, prove `Challenge.Blake2f.Correct bytecode`.
Correctness covers every realizable calldata: exact 64-byte output for valid
213-byte EIP-152 input and exceptional failure otherwise. Address `0x09` is
disabled in the specified frame.

Create an UpperCamelCase directory containing:

```text
Challenge/Blake2f/Submissions/FastBlake2f/
  bytecode.hex
  Bytecode.lean
  Proof.lean
  Gas.lean       # optional
  README.md
```

Hex is canonical lowercase byte pairs without `0x`. `Bytecode.lean` exposes
`bytecode`; `Proof.lean` exposes exactly:

```lean
theorem correct : Challenge.Blake2f.Correct bytecode := by
  -- proof
```

The stable direct target is
`Challenge.Blake2f.ProofSupport.Bytecode.DirectProof bytecode`. The verified
source alternative is `ProofSupport.Yul.ComputesBehavior`, including malformed
input `invalid()` behavior.

Optional gas proofs define a `GasFormula`, its evaluator schedule, and prove
`CorrectWithSchedule bytecode gasSchedule`. Formulas may use calldata size,
round count, final flag, validity, constants, addition, and multiplication.
Universal proofs may use only Lean's standard logical axioms; measurements and
fixed-artifact `native_decide` checks are not correctness proofs.
