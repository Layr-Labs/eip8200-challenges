# SHA-256 challenge: audit map

This directory is layered so that agreeing with the challenge does not require
auditing the bundled implementation or its proof engineering.

## 1. Minimal specification

Read [`Spec.lean`](Spec.lean). It defines only:

- `spec`: the SHA-256 function used by the pinned EVM semantics;
- `CalldataFits`: the realizable-input bound;
- `initialState`: the fixed initial EVM state used to run a candidate; and
- `Correct code`: eventual return of exactly `spec calldata` for every fitting
  input and every sufficiently large gas budget.

`initialState` is a repository-defined constructor, not a protocol object
called a "canonical frame." It fixes code, calldata, gas, fork, and all ambient
fields explicitly. [`AdditionalGoals/AnyContext.lean`](AdditionalGoals/AnyContext.lean)
states the optional stronger property that the result is independent of caller,
call value, storage, address, and surrounding world state.

`Spec.lean` imports only the pinned EVM big-step semantics. It does not import
the compiler, reference artifact, scorer, or proof support. CI pins this
one-way dependency boundary.

## 2. Making a contribution

Read [`SUBMITTING.md`](SUBMITTING.md). It specifies the directory and namespace
convention, required `bytecode` value and `correct : Correct bytecode` theorem,
local commands, direct-EVM proof tools, and the automatic CI proof gate.

## 3. Reusable proof support

[`ProofSupport/`](ProofSupport/) contains implementation-independent ways to
reach `Correct`:

- [`ProofSupport/Bytecode.lean`](ProofSupport/Bytecode.lean) defines the direct
  raw-bytecode obligation and its soundness theorem;
- [`ProofSupport/Yul.lean`](ProofSupport/Yul.lean) is an optional
  verified-compiler reduction for contributors who want to prove their Yul; and
- [`ProofSupport/InitialState.lean`](ProofSupport/InitialState.lean) contains
  small projection lemmas about `initialState`.

The challenge-independent disassembly and EVM execution machinery lives in
[`../EvmProof/`](../EvmProof/).

## 4. Bundled reference

[`Reference/`](Reference/) contains everything tied to the baseline:

- `reference.yul`: readable source used to generate the artifact;
- `reference.hex`: frozen compiler output;
- `Bytes.lean`: the reducible byte literal used by concrete execution proofs;
- `Bytecode.lean`: artifact and byte-preservation facts; and
- [`Proofs/Bytecode/`](Reference/Proofs/Bytecode/): the complete direct EVM
  proof, ending at `ReferenceCorrect.reference_correct : Correct referenceBytecode`.

The reference is proved correct directly as bytecode. Its Yul source does not
need a second functional-correctness proof.

## 5. Non-proof tooling

[`Scorer.lean`](Scorer.lean) and the repository-root `Main.lean` implement the
finite Tier-1 test runner. Passing it is useful evidence, never a proof.

The umbrella modules `ProofSupport.lean`, `AdditionalGoals.lean`,
`Reference.lean`, and `Reference/Proofs.lean` expose each layer without mixing
their dependencies.
