import Challenge.RouteB
import Challenge.Sha256.Bytecode
import Challenge.Sha256.Statement
import Challenge.Sha256.Reduction
import Challenge.Sha256.Reference
import Challenge.Sha256.RouteB
import Challenge.Sha256.RouteB.Reference
import Challenge.Sha256.RouteB.Main
import Challenge.Sha256.RouteB.Padding
import Challenge.Sha256.RouteB.PaddingTrace
import Challenge.Sha256.RouteB.Trace
import Challenge.Sha256.RouteB.Word
import Challenge.Sha256.Scorer
set_option warningAsError true
/-!
# EIP-8200 challenges

Verified replacements for Ethereum precompiles: EVM bytecode, plus a
machine-checked proof that the bytecode computes what the precompile
computed.

SHA-256 (`0x02`) is the pilot:

* `Challenge.RouteB` — verified disassembly and direct small-step proof
  combinators for raw-bytecode submissions.
* `Challenge.Sha256.Bytecode` — the frozen 1,524-byte reference artifact.
* `Challenge.Sha256.Statement` — `Correct`, the statement every submission
  must satisfy, and the frame it is judged in.
* `Challenge.Sha256.Reduction` — the reduction that discharges it for
  bytecode the verified Yul compiler produced, leaving a Yul-level
  obligation as the only open goal.
* `Challenge.Sha256.Reference` — the reference submission
  (`Challenge/Sha256/reference.yul`) and its end-to-end theorem modulo the
  named obligations.
* `Challenge.Sha256.RouteB` — the submission-facing direct-bytecode obligation
  and its reduction to `Correct`.
* `Challenge.Sha256.Scorer` — Tier 1, falsification by execution
  (`lake exe sha256challenge`).

`README.md` is the challenge document: the tiers, the submission routes, and
the open obligations.
-/
