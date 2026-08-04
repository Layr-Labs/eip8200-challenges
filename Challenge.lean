import Challenge.EvmProof
import Challenge.Ripemd160
import Challenge.Sha256
set_option warningAsError true
/-!
# EIP-8200 challenges

Verified replacements for Ethereum precompiles: EVM bytecode, plus a
machine-checked proof that the bytecode computes what the precompile
computed.

SHA-256 (`0x02`) and RIPEMD-160 (`0x03`) are the first challenges:

* `Challenge.EvmProof` — verified disassembly and direct small-step proof
  combinators for raw-bytecode submissions.
* `Challenge.Sha256.Spec` — the minimal auditor-facing `Correct` predicate and
  fixed initial EVM state it quantifies over.
* `Challenge.Sha256.ProofSupport` — reusable Yul and direct-bytecode reductions
  and initial-state lemmas for proving `Correct`.
* `Challenge.Sha256.Reference` — the bundled Yul and frozen 1,524-byte artifact.
* `Challenge.Sha256.Reference.Proofs` — implementation-specific correctness
  proofs, including the complete direct EVM proof of the frozen bytes.
* `Challenge.Sha256.Scorer` — Tier 1, falsification by execution
  (`lake exe sha256challenge`).
* `Challenge.Ripemd160.Spec` — the minimal RIPEMD-160 precompile-equivalence
  statement.
* `Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect` — the
  unconditional direct-bytecode correctness and exact-gas theorems.
* `Challenge.Ripemd160.Scorer` — executable clean- and dirty-memory vectors
  (`lake exe ripemd160challenge`).

See each challenge directory for its specification, audit map, submission
instructions, reference artifact, and proof.
-/
