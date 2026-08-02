import Challenge.BytecodeProof
import Challenge.Sha256
set_option warningAsError true
/-!
# EIP-8200 challenges

Verified replacements for Ethereum precompiles: EVM bytecode, plus a
machine-checked proof that the bytecode computes what the precompile
computed.

SHA-256 (`0x02`) is the pilot:

* `Challenge.BytecodeProof` — verified disassembly and direct small-step proof
  combinators for raw-bytecode submissions.
* `Challenge.Sha256.Spec` — the minimal auditor-facing `Correct` predicate and
  the canonical EVM frame it quantifies over.
* `Challenge.Sha256.ProofSupport` — reusable Yul and direct-bytecode reductions
  and frame lemmas for proving `Correct`.
* `Challenge.Sha256.Reference` — the bundled Yul and frozen 1,524-byte artifact.
* `Challenge.Sha256.Reference.Proofs` — implementation-specific correctness
  proofs, including the complete direct EVM proof of the frozen bytes.
* `Challenge.Sha256.Scorer` — Tier 1, falsification by execution
  (`lake exe sha256challenge`).

`README.md` is the challenge document: the tiers, the submission approaches, and
the open obligations.
-/
