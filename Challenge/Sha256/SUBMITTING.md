# Submitting SHA-256 bytecode

This document is the mechanical contract for a candidate PR. It is written for
both human contributors and coding agents.

## Required result

For concrete EVM bytecode `bytecode`, prove:

```lean
Challenge.Sha256.Correct bytecode
```

`Correct` is defined in [`Spec.lean`](Spec.lean). It runs the bytes from the
fixed `initialState` for every realizable calldata and requires exactly the
32-byte SHA-256 digest for every sufficiently large gas budget.

Read `Spec.lean` before starting. It is the complete required functional
statement. Properties under [`AdditionalGoals/`](AdditionalGoals/) are useful
strengthenings, but are not required for an ordinary correctness submission.

## Directory and names

Choose an UpperCamelCase Lean identifier for the candidate, such as
`FastSha256`, and add exactly one directory:

```text
Challenge/Sha256/Submissions/FastSha256/
  bytecode.hex
  Bytecode.lean
  Proof.lean
  README.md
```

Use namespace `Challenge.Sha256.Submissions.FastSha256`. CI derives the module
and declaration names from the directory name, so the convention is mandatory.

`bytecode.hex` contains one line of lowercase hexadecimal EVM bytes without a
`0x` prefix. A final newline is allowed. This canonical representation lets CI
compare the file with the byte array without trusting a lenient parser.

`Bytecode.lean` must expose `bytecode : ByteArray`. The simplest form is:

```lean
import EvmSemantics.Data.Hex

namespace Challenge.Sha256.Submissions.FastSha256

def bytecodeHex : String := (include_str "bytecode.hex").trimAscii.copy
def bytecode : ByteArray := EvmSemantics.Hex.hexToBytes bytecodeHex

end Challenge.Sha256.Submissions.FastSha256
```

A large direct-execution proof may instead use generated reducible byte chunks,
as the bundled reference does. That is fine: CI independently checks that
`EvmSemantics.Hex.bytesToHex bytecode` equals `bytecode.hex`.

`Proof.lean` must expose the theorem with this exact name and type:

```lean
import Challenge.Sha256.Submissions.FastSha256.Bytecode
import Challenge.Sha256.ProofSupport.Bytecode

namespace Challenge.Sha256.Submissions.FastSha256

theorem correct : Challenge.Sha256.Correct bytecode := by
  -- proof

end Challenge.Sha256.Submissions.FastSha256
```

`README.md` should state the implementation strategy, provenance of the bytes,
measured gas, and the main proof invariants. It is explanatory; CI never treats
it as evidence of correctness.

## Direct bytecode proofs

The stable SHA-specific target is:

```lean
Challenge.Sha256.ProofSupport.Bytecode.DirectProof bytecode
```

and

```lean
Challenge.Sha256.ProofSupport.Bytecode.correct_of_directProof
```

turns that result into `Correct bytecode`.

[`Challenge/EvmProof/`](../EvmProof/) is the challenge-independent proof
toolkit:

- `Bytecode.lean`: byte-preserving disassembly and jump-destination facts;
- `Execution.lean`: `Step`, `Eval`, `Reaches`, and straight-line composition;
- `Stepper.lean`: executable instruction-block proofs;
- `Gas.lean`: gas-erased traces, bounded-loop composition, and the final
  `EventuallyEvaluates` bridge;
- `Memory.lean` and `Word.lean`: common EVM memory and 256-bit arithmetic facts;
- `Ops.lean` and `Program.lean`: reusable opcode and program-artifact support.

A natural proof decomposition is:

1. Freeze and disassemble the submitted bytes.
2. Name control-flow entry points and the machine state expected at each one.
3. Prove straight-line basic blocks with the executable stepper.
4. Compose blocks and loops with `Reaches` or `GasSteps`, stating one invariant
   per loop.
5. Relate padding, schedule, compression, and output memory to the SHA
   functions used by `Challenge.Sha256.spec`.
6. Prove the terminal state returns the digest and use
   `GasSteps.toEventuallyEvaluates` to discharge `DirectProof`.

The bundled proof under [`Reference/Proofs/Bytecode/`](Reference/Proofs/Bytecode/)
is a worked example, but its program counters and memory layout are reference
implementation details. An optimized candidate should reuse the generic
toolkit and functional seams, not copy those concrete states blindly.

## Optional verified-Yul path

[`ProofSupport/Yul.lean`](ProofSupport/Yul.lean) provides an alternative
reduction for a contributor who wants to prove a Yul program and rely on the
verified compiler. It is optional. The bundled reference already has a direct
proof of its final bytes and therefore needs no second Yul correctness proof.

Regardless of proof strategy, the PR must still expose the same concrete
`bytecode` and `correct : Correct bytecode` declarations.

## Local checks

Run:

```sh
lake exe cache get
lake build
lake exe sha256challenge --hex=Challenge/Sha256/Submissions/FastSha256/bytecode.hex
scripts/check-sha256-submissions.sh
```

The submission checker discovers every immediate subdirectory of
`Challenge/Sha256/Submissions/` and verifies:

1. all four required files exist;
2. `Proof.lean` imports and `correct` has exactly the required type;
3. the Lean `bytecode` is byte-for-byte equal to `bytecode.hex`;
4. the transitive axiom set of `correct` contains only `propext`,
   `Classical.choice`, and `Quot.sound`; and
5. the exact hex artifact passes the executable SHA scorer.

Thus `sorry`, `native_decide`, a project-defined `axiom`, a theorem about a
different byte array, or a proof paired with different hex all fail CI. The CI
job also runs the checker against a deliberately fake axiom as a negative
control.

## PR guidance

Keep a candidate PR confined to its new submission directory whenever
possible. Changes to `Spec.lean`, the central checker, proof support, pinned
dependencies, or CI alter the trust boundary and should be proposed as a
separate infrastructure PR.
